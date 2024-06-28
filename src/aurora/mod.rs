use ark_std::{log2, rand::RngCore};

use ark_crypto_primitives::sponge::{Absorb, CryptographicSponge};
use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain,
    Polynomial,
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
    /// Commitments to f_a, f_b, f_c, f_0, f_w and g_1
    /// These should have an enforced degree bound <= n - 1, where n is the
    /// number of columns of the R1CS
    large_coms: Vec<LabeledCommitment<PCS::Commitment>>,
    /// Commitment to g_2
    /// This should have an enforced degree bound <= n - 2
    com_g_2: LabeledCommitment<PCS::Commitment>,
    /// Proofs of opening for the large commitments
    large_opening_proof: PCS::Proof,
    /// Proof of opening for the small commitment
    g_2_opening_proof: PCS::Proof,
    /// Values f_a(a), f_b(a), f_c(a), f_0(a), f_w(a), g_1(a)
    large_evals: Vec<F>,
    /// Value g_2(a)
    g_2_a: F,
}

#[derive(Clone)]
pub struct AuroraR1CS<F>
where
    F: PrimeField + Absorb,
{
    r1cs: ConstraintSystem<F>,
    pub(crate) unpadded_num_instance_variables: usize,
}

/// Aurora prover key, containing the R1CS and PCS keys to commit
/// to polynomials of degree <= n - 1 and <= n - 2
pub struct AuroraProverKey<F, PCS>
where
    F: PrimeField + Absorb,
    PCS: PolynomialCommitment<F, DensePolynomial<F>>,
{
    pub(crate) r1cs: AuroraR1CS<F>,
    // Committer PCS key enforcing the degree bound <= n - 1, where
    // n is the number of columns of the (padded) R1CS
    pub(crate) ck_large: PCS::CommitterKey,
    // Committer PCS key enforcing the degree bound <= n - 2
    pub(crate) ck_small: PCS::CommitterKey,
}

// Aurora verifier key, containing the R1CS and PCS keys to  verify
// commitments to polynomials of degree <= n - 1 and <= n - 2
pub struct AuroraVerifierKey<F, PCS>
where
    F: PrimeField + Absorb,
    PCS: PolynomialCommitment<F, DensePolynomial<F>>,
{
    pub(crate) r1cs: AuroraR1CS<F>,
    // Verifier PCS key enforcing the degree bound <= n - 1, where n is the
    // number of columns of the (padded) R1CS
    pub(crate) vk_large: PCS::VerifierKey,
    // CVerifier PCS key enforcing the degree bound <= n - 2
    pub(crate) vk_small: PCS::VerifierKey,
}

impl<F> AuroraR1CS<F>
where
    F: PrimeField + Absorb,
{
    pub fn setup<PCS: PolynomialCommitment<F, DensePolynomial<F>>>(
        r1cs: ConstraintSystem<F>,
        rng: &mut impl RngCore,
    ) -> Result<(AuroraProverKey<F, PCS>, AuroraVerifierKey<F, PCS>), AuroraError<F, PCS>> {
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
        let (ck_large, vk_large) = PCS::trim(&pp, n - 1, 0, Some(&[n - 1]))
            .map_err(|e| AuroraError::<F, PCS>::PCSError(e))
            .unwrap();
        let (ck_small, vk_small) = PCS::trim(&pp, n - 2, 0, Some(&[n - 2]))
            .map_err(|e| AuroraError::<F, PCS>::PCSError(e))
            .unwrap();

        Ok((
            AuroraProverKey {
                r1cs: aurora_r1cs.clone(),
                ck_large,
                ck_small,
            },
            AuroraVerifierKey {
                r1cs: aurora_r1cs.clone(),
                vk_large,
                vk_small,
            },
        ))
    }

    pub fn prove<PCS: PolynomialCommitment<F, DensePolynomial<F>>>(
        pk: &AuroraProverKey<F, PCS>,
        instance: Vec<F>,
        witness: Vec<F>,
        // In the future, consider whether this should nestead be PCS::UniversalParams
        pcs_vks: (&PCS::VerifierKey, &PCS::VerifierKey),
        sponge: &mut impl CryptographicSponge,
    ) -> Result<AuroraProof<F, PCS>, AuroraError<F, PCS>> {
        let AuroraProverKey {
            r1cs:
                AuroraR1CS {
                    r1cs,
                    unpadded_num_instance_variables,
                },
            ck_large,
            ck_small,
        } = pk;

        assert_padded(&r1cs);

        let matrices = r1cs.to_matrices().unwrap();

        // 0. Initialising sponge with public parameters
        absorb_public_parameters::<F, PCS>(pcs_vks, &matrices, sponge);

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
        if instance.len() != *unpadded_num_instance_variables {
            return Err(AuroraError::IncorrectInstanceLength {
                received: instance.len(),
                expected: *unpadded_num_instance_variables,
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

        // ======================== Computation of f_w and f_z ========================

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

        // ================== Committing to f_a, f_b, f_c, f_0 and f_w ==================

        let labeled_polynomials_1 = label_polynomials(&[
            ("f_a", &f_a),
            ("f_b", &f_b),
            ("f_c", &f_c),
            ("f_0", &f_0),
            ("f_w", &f_w),
        ]);

        // Commiting to all the polynomials with enforced degree bound <= n - 1:
        // f_a, f_b, f_c, f_0, f_w
        let (com_1, com_states_1) = PCS::commit(ck_large, &labeled_polynomials_1, None).unwrap();

        sponge.absorb(&com_1);

        // ======================== Computation of g_1 and g_2 ========================

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

        // We construct g_1 and g_2 such that u = v_h * g_1 + x * g_2 and with
        // prescribed degree bounds
        let (g_1, remainder) = u.divide_by_vanishing_poly(h).unwrap();
        let g_2 = &remainder / &monomial(1);

        //==================== Committing to g_1 and g_2 ====================

        let labeled_g_1 = label_polynomials(&[("g_1", &g_1)]);
        let labeled_g_2 = label_polynomials(&[("g_2", &g_2)]);

        // ck_large, ck_small enforce the degree bound <= n - 1 and <= n - 2 for
        // g_1 and g_2, respectively
        let (com_g_1, g_1_com_state) = PCS::commit(&ck_large, &labeled_g_1, None).unwrap();
        let (mut com_g_2, g_2_com_state) = PCS::commit(&ck_small, &labeled_g_2, None).unwrap();

        sponge.absorb(&com_g_1);
        sponge.absorb(&com_g_2);

        let large_coms = [com_1, com_g_1].concat();
        let large_com_states = [com_states_1, g_1_com_state].concat();
        let large_labeled_polynomials = [labeled_polynomials_1, labeled_g_1].concat();

        //======================== PCS proof ========================

        let a_point: F = sponge.squeeze_field_elements(1)[0];

        let large_opening_proof = PCS::open(
            &ck_large,
            &large_labeled_polynomials,
            &large_coms,
            &a_point,
            sponge,
            &large_com_states,
            None,
        )
        .unwrap();

        let g_2_opening_proof = PCS::open(
            &ck_small,
            &labeled_g_2,
            &com_g_2,
            &a_point,
            sponge,
            &g_2_com_state,
            None,
        )
        .unwrap();

        Ok(AuroraProof {
            large_coms,
            com_g_2: com_g_2.remove(0),
            large_opening_proof,
            g_2_opening_proof,
            large_evals: large_labeled_polynomials
                .iter()
                .map(|lp| lp.evaluate(&a_point))
                .collect(),
            g_2_a: g_2.evaluate(&a_point),
        })
    }

    pub fn verify<PCS: PolynomialCommitment<F, DensePolynomial<F>>>(
        vk: &AuroraVerifierKey<F, PCS>,
        instance: Vec<F>,
        aurora_proof: AuroraProof<F, PCS>,
        sponge: &mut impl CryptographicSponge,
    ) -> Result<bool, AuroraError<F, PCS>> {
        let AuroraVerifierKey {
            r1cs:
                AuroraR1CS {
                    r1cs,
                    unpadded_num_instance_variables,
                },
            vk_large,
            vk_small,
        } = vk;

        assert_padded(&r1cs);

        let matrices = r1cs.to_matrices().unwrap();

        // 0. Initialising sponge with public parameters
        absorb_public_parameters::<F, PCS>((&vk_large, &vk_small), &matrices, sponge);

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
            large_coms,
            com_g_2,
            large_opening_proof,
            g_2_opening_proof,
            large_evals,
            g_2_a,
        } = aurora_proof;

        // Checking instance and witness lengths
        if instance.len() != *unpadded_num_instance_variables {
            return Err(AuroraError::IncorrectInstanceLength {
                received: instance.len(),
                expected: *unpadded_num_instance_variables,
            });
        }

        // Resize the instance to the padded length
        let mut instance = instance;
        instance.resize(num_instance_variables, F::ZERO);

        // Absorb the first 5 commitments
        sponge.absorb(&large_coms.iter().take(5).collect::<Vec<_>>());

        let r: F = sponge.squeeze_field_elements(1)[0];

        // ======================== Verify the proof ========================

        // Absorb the missing commitments to g1, g2
        sponge.absorb(&large_coms.last().unwrap());
        sponge.absorb(&com_g_2);

        let a_point: F = sponge.squeeze_field_elements(1)[0];

        if !PCS::check(
            vk_large,
            &large_coms,
            &a_point,
            large_evals.clone(),
            &large_opening_proof,
            sponge,
            None,
        )
        .unwrap()
        {
            return Ok(false);
        }

        if !PCS::check(
            vk_small,
            &[com_g_2],
            &a_point,
            vec![g_2_a],
            &g_2_opening_proof,
            sponge,
            None,
        )
        .unwrap()
        {
            return Ok(false);
        }

        // ======================== Zero test ========================

        // Evaluations of the committed polynomials at a_point
        let [f_a_a, f_b_a, f_c_a, f_0_a, f_w_a, g_1_a] = large_evals[..] else {
            return Err(AuroraError::IncorrectNumberOfEvaluations {
                received: large_evals.len(),
                expected: 6,
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
