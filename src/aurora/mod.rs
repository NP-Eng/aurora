use ark_std::{log2, rand::RngCore};

use ark_crypto_primitives::sponge::{Absorb, CryptographicSponge};
use ark_ff::PrimeField;
use ark_poly::{
    univariate::{DensePolynomial, SparsePolynomial},
    DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain,
};
use ark_poly_commit::{LabeledCommitment, PolynomialCommitment};
use ark_relations::r1cs::{ConstraintMatrices, ConstraintSystem};
use error::AuroraError;
use utils::*;

#[cfg(test)]
mod tests;

mod error;
mod utils;

pub struct AuroraProof<F, PCS>
where
    F: PrimeField,
    PCS: PolynomialCommitment<F, DensePolynomial<F>>,
{
    commitments: Vec<LabeledCommitment<PCS::Commitment>>,
    proof: PCS::Proof,
    evals: Vec<F>,
}

pub struct AuroraR1CS<F>
where
    F: PrimeField + Absorb,
{
    r1cs: ConstraintSystem<F>,
    unpadded_num_instance_variables: usize,
}

impl<F> AuroraR1CS<F>
where
    F: PrimeField + Absorb,
{
    pub fn setup<PCS: PolynomialCommitment<F, DensePolynomial<F>>>(
        r1cs: ConstraintSystem<F>,
        rng: &mut impl RngCore,
    ) -> Result<(AuroraR1CS<F>, PCS::CommitterKey, PCS::VerifierKey), AuroraError<F, PCS>> {
        let unpadded_num_instance_variables = r1cs.num_instance_variables;

        let mut r1cs = r1cs;

        pad_r1cs(&mut r1cs);

        let n = r1cs.num_constraints;

        if 1 << F::TWO_ADICITY < n {
            panic!(
                "The field F has 2-Sylow subgroup of order 2^{}, but the R1CS requires 2^{}",
                F::TWO_ADICITY,
                log2(n)
            );
        }

        let aurora_r1cs = AuroraR1CS {
            r1cs,
            unpadded_num_instance_variables,
        };

        // TODO make sure Ligero is enforcing the degree bound
        let pp = PCS::setup(n - 1, None, rng).unwrap();

        // No hiding needed, as this version of Aurora is not zero-knowledge
        let result = PCS::trim(&pp, n - 1, 0, Some(&[n - 1]));

        result
            .map(|(ck, vk)| (aurora_r1cs, ck, vk))
            .map_err(|e| AuroraError::PCSError(e))
    }

    pub fn prove<PCS: PolynomialCommitment<F, DensePolynomial<F>>>(
        &mut self,
        instance: Vec<F>,
        witness: Vec<F>,
        ck: &PCS::CommitterKey,
        vk: &PCS::VerifierKey,
        sponge: &mut impl CryptographicSponge,
    ) -> Result<AuroraProof<F, PCS>, AuroraError<F, PCS>> {
        assert_padded(&self.r1cs);

        let matrices = self.r1cs.to_matrices().unwrap();

        // 0. Initialising sponge with public parameters
        absorb_public_parameters::<F, PCS>(&vk, &matrices, sponge);

        let ConstraintMatrices {
            a,
            b,
            c,
            num_constraints: n,
            num_instance_variables,
            num_witness_variables,
            ..
        } = matrices;

        // Checking instance and witness lengths
        if instance.len() != self.unpadded_num_instance_variables {
            return Err(AuroraError::IncorrectInstanceLength {
                received: instance.len(),
                expected: self.unpadded_num_instance_variables,
            });
        }

        if witness.len() != num_witness_variables {
            return Err(AuroraError::IncorrectWitnessLength {
                received: witness.len(),
                expected: num_witness_variables,
            });
        }

        // Resize the instance to the padded length
        let mut instance = instance;
        instance.resize(num_instance_variables, F::ZERO);

        // 1. Constructing committed polynomials
        // Following the notation of the paper
        let h = GeneralEvaluationDomain::new(n).unwrap();

        let solution = [instance.clone(), witness.clone()].concat();

        // ======================== Computation of f_0 ========================

        // Note we can't compute f_a * f_b using an iFFT
        let f_a = matrix_polynomial(&a, &solution, &h);
        let f_b = matrix_polynomial(&b, &solution, &h);
        let f_c = matrix_polynomial(&c, &solution, &h);

        // Computing f_0 = (f_a * f_b - f_c) / v_h
        let f_0 = (&(&f_a * &f_b) - &f_c)
            .divide_by_vanishing_poly(h)
            .unwrap()
            .0;

        // ======================== Computation of f_w ========================

        let zero_padded_witness = [vec![F::ZERO; num_instance_variables], witness.clone()].concat();

        // Return the unique polynomial of degree < n that interpolates the given
        // values over h
        let h_interpolate = |evals: &Vec<F>| DensePolynomial::from_coefficients_vec(h.ifft(&evals));

        // Numerator
        let z_minus_v_star = h_interpolate(&zero_padded_witness);

        // TODO: Is there a more efficient way to compute this?
        // Denominator v_h_in = (x - 1) * (x - zeta^1) * ... * (x - zeta^(k-1))
        let v_h_in = h
            .elements()
            .take(num_instance_variables) // 1, zeta, ..., zeta^(k-1)
            .map(|c| DensePolynomial::from_coefficients_slice(&[-c, F::ONE])) // x - zeta^i
            .reduce(|acc, p| &acc * &p) // multiply together
            .unwrap();

        let f_w = &z_minus_v_star / &v_h_in;

        // ======================== Computation of f_z ========================

        let f_z = h_interpolate(&solution);

        // ================== Committing to f_a, f_b, f_c, f_0, f_w ==================

        let labeled_polynomials_1 = label_polynomials(&[
            ("f_a", &f_a),
            ("f_b", &f_b),
            ("f_c", &f_c),
            ("f_0", &f_0),
            ("f_w", &f_w),
        ]);

        let (com_1, com_states_1) = PCS::commit(ck, &labeled_polynomials_1, None).unwrap();

        sponge.absorb(&com_1);

        // ======================== Computation of g_1, g_2 ========================

        // Randomising polinomial through a squeezed challenge
        let r: F = sponge.squeeze_field_elements(1)[0];

        // Computing [1, r, r^2, ... r^(n-1)]
        let powers_of_r = powers(r, n);
        let p_r = h_interpolate(&powers_of_r);

        let q_ar = h_interpolate(&random_matrix_polynomial_evaluations(&a, &powers_of_r));
        let q_br = h_interpolate(&random_matrix_polynomial_evaluations(&b, &powers_of_r));
        let q_cr = h_interpolate(&random_matrix_polynomial_evaluations(&c, &powers_of_r));

        let r_pow_n = r * powers_of_r[n - 1];

        let u = (&(&p_r * &f_a) - &(&q_ar * &f_z))
            + &(&(&p_r * &f_b) - &(&q_br * &f_z)) * r_pow_n
            + &(&(&p_r * &f_c) - &(&q_cr * &f_z)) * (r_pow_n * r_pow_n);

        // We construct g_1 and g_2 such that u = v_h * g_1 + x * g_2

        // Auxiliary polynomials x and x^n - 1
        let x = DensePolynomial::from(SparsePolynomial::from_coefficients_slice(&[(1, F::ONE)]));

        let x_n_minus_1 = DensePolynomial::from(SparsePolynomial::from_coefficients_slice(&[(
            n - 1,
            F::ONE,
        )]));

        let dividend = &x_n_minus_1 * &u;

        let (quotient, g_2) = dividend.divide_by_vanishing_poly(h).unwrap();

        let g_1 = &(&quotient * &x) - &u;

        //==================== Committing to g_1, g_2 ====================

        let labeled_polynomials_2 = label_polynomials(&[("g_1", &g_1), ("g_2", &g_2)]);

        let (com_2, com_states_2) = PCS::commit(ck, &labeled_polynomials_2, None).unwrap();

        sponge.absorb(&com_2);

        let coms = [com_1, com_2].concat();
        let com_states = [com_states_1, com_states_2].concat();
        let labeled_polynomials = [labeled_polynomials_1, labeled_polynomials_2].concat();

        //======================== PCS proof ========================

        let a_point: F = sponge.squeeze_field_elements(1)[0];

        let proof = PCS::open(
            ck,
            &labeled_polynomials,
            &coms,
            &a_point,
            sponge,
            &com_states,
            None,
        )
        .unwrap();

        Ok(AuroraProof {
            commitments: coms,
            proof,
            evals: labeled_polynomials
                .iter()
                .map(|lp| lp.evaluate(&a_point))
                .collect(),
        })
    }

    pub fn verify<PCS: PolynomialCommitment<F, DensePolynomial<F>>>(
        &self,
        vk: &PCS::VerifierKey,
        instance: Vec<F>,
        aurora_proof: AuroraProof<F, PCS>,
        sponge: &mut impl CryptographicSponge,
    ) -> Result<bool, AuroraError<F, PCS>> {
        assert_padded(&self.r1cs);

        let matrices = self.r1cs.to_matrices().unwrap();

        // 0. Initialising sponge with public parameters
        absorb_public_parameters::<F, PCS>(vk, &matrices, sponge);

        let ConstraintMatrices {
            a,
            b,
            c,
            num_constraints: n,
            num_instance_variables,
            num_witness_variables,
            ..
        } = matrices;

        let AuroraProof {
            commitments: com,
            proof,
            evals,
        } = aurora_proof;

        // Checking instance and witness lengths
        if instance.len() != self.unpadded_num_instance_variables {
            return Err(AuroraError::IncorrectInstanceLength {
                received: instance.len(),
                expected: self.unpadded_num_instance_variables,
            });
        }

        // Resize the instance to the padded length
        let mut instance = instance;
        instance.resize(num_instance_variables, F::ZERO);

        // Absorb the first 5 commitments
        sponge.absorb(&com.iter().take(5).collect::<Vec<_>>());

        let r: F = sponge.squeeze_field_elements(1)[0];

        // ======================== Verify the proof ========================

        // Absorb the missing commitments to g1, g2
        sponge.absorb(&com.iter().skip(5).collect::<Vec<_>>());

        let a_point: F = sponge.squeeze_field_elements(1)[0];

        if !PCS::check(vk, &com, &a_point, evals.clone(), &proof, sponge, None).unwrap() {
            return Ok(false);
        }

        // ======================== Zero test ========================

        // Evaluations of the committed polynomials at a_point
        let [f_a_a, f_b_a, f_c_a, f_0_a, f_w_a, g_1_a, g_2_a] = evals[..] else {
            return Err(AuroraError::IncorrectNumberOfEvaluations {
                received: evals.len(),
                expected: 7,
            });
        };

        let h = GeneralEvaluationDomain::<F>::new(n).unwrap();

        let v_h_a = h.evaluate_vanishing_polynomial(a_point);

        if f_a_a * f_b_a - f_c_a != f_0_a * v_h_a {
            return Ok(false);
        }

        // ======================== Univariate sumcheck test ========================
        let zero_padded_instance =
            [instance.clone(), vec![F::ZERO; num_witness_variables]].concat();

        let lagrange_basis_evals = h.evaluate_all_lagrange_coefficients(a_point);

        // Returns f(a_point), where f is the unique polynomial of degree < n that
        // interpolates the given values over h. This requires
        //  - a one-time evaluation of the Lagrange basis over h at a_point
        //    (lagrange_basis_evals), which is amortised over all calls
        //  - a one-time inner product of size n per call.
        let h_evaluate_interpolator = |evals: &Vec<F>| inner_product(&evals, &lagrange_basis_evals);

        let v_star_a = h_evaluate_interpolator(&zero_padded_instance);

        let v_h_in_a: F = h
            .elements()
            .take(num_instance_variables)
            .map(|c| a_point - c)
            .product();

        let f_z_a = f_w_a * v_h_in_a + v_star_a;

        // Computing [1, r, r^2, ... r^(n-1)]
        let powers_of_r = powers(r, n);
        let p_r_a = h_evaluate_interpolator(&powers_of_r);

        let q_ar_a =
            h_evaluate_interpolator(&random_matrix_polynomial_evaluations(&a, &powers_of_r));
        let q_br_a =
            h_evaluate_interpolator(&random_matrix_polynomial_evaluations(&b, &powers_of_r));
        let q_cr_a =
            h_evaluate_interpolator(&random_matrix_polynomial_evaluations(&c, &powers_of_r));

        let r_pow_n = r * powers_of_r[n - 1];

        let u_a = (p_r_a * f_a_a - q_ar_a * f_z_a)
            + (p_r_a * f_b_a - q_br_a * f_z_a) * r_pow_n
            + (p_r_a * f_c_a - q_cr_a * f_z_a) * (r_pow_n * r_pow_n);

        Ok(u_a == g_1_a * v_h_a + g_2_a * a_point)
    }

    // Returns the internal R1CS. Note that it is padded upon calling
    // Aurora::setup
    pub fn r1cs(&self) -> &ConstraintSystem<F> {
        &self.r1cs
    }
}
