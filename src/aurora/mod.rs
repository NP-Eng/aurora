use ark_std::{log2, rand::RngCore};

use ark_crypto_primitives::sponge::{Absorb, CryptographicSponge};
use ark_ff::PrimeField;
use ark_poly::{
    univariate::{DensePolynomial, SparsePolynomial},
    DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain, Polynomial,
};
use ark_poly_commit::{LabeledCommitment, LabeledPolynomial, PolynomialCommitment};
use ark_relations::r1cs::{ConstraintMatrices, ConstraintSystem, LinearCombination, Matrix};
use ark_std::cmp::max;

use crate::utils::{powers, sparse_matrix_by_vec};

#[cfg(test)]
mod tests;

pub struct AuroraProof<F, PCS>
where
    F: PrimeField + Absorb,
    PCS: PolynomialCommitment<F, DensePolynomial<F>>,
{
    commitments: Vec<LabeledCommitment<PCS::Commitment>>,
    proof: PCS::Proof,
    evals: Vec<F>,
}

pub(crate) fn is_padded<F: PrimeField>(r1cs: &ConstraintSystem<F>) -> bool {
    let sol_len = r1cs.num_instance_variables + r1cs.num_witness_variables;
    r1cs.num_instance_variables.is_power_of_two()
        && sol_len.is_power_of_two()
        && sol_len == r1cs.num_constraints
}

// TODO remove padding of v
pub(crate) fn pad_r1cs<F: PrimeField>(r1cs: &mut ConstraintSystem<F>) {
    let padded_instance_len = r1cs.num_instance_variables.next_power_of_two();
    let prepadded_sol_len = padded_instance_len + r1cs.num_witness_variables;

    let padded_len = max(prepadded_sol_len, r1cs.num_constraints).next_power_of_two();

    r1cs.num_instance_variables = padded_instance_len;
    r1cs.num_witness_variables = padded_len - padded_instance_len;

    if !r1cs.instance_assignment.is_empty() {
        r1cs.instance_assignment
            .resize(padded_instance_len, F::ZERO);
    }

    if !r1cs.witness_assignment.is_empty() {
        r1cs.witness_assignment
            .resize(r1cs.num_witness_variables, F::ZERO);
    }

    // Padding rows
    (0..padded_len - r1cs.num_constraints).for_each(|_| {
        r1cs.enforce_constraint(
            LinearCombination::zero(),
            LinearCombination::zero(),
            LinearCombination::zero(),
        )
        .unwrap();
    });

    // TODO Decide what to do with unclear fields:
    // - #[cfg(feature = "std")]
    //    constraint_traces: Vec<Option<ConstraintTrace>>,
    // - pub cache_map: Rc<RefCell<BTreeMap<TypeId, Box<dyn Any>>>>,
    // - lc_assignment_cache: Rc<RefCell<BTreeMap<LcIndex, F>>>,
}

fn matrix_polynomial<F: PrimeField>(
    m: &Matrix<F>,
    z: &Vec<F>,
    domain: &GeneralEvaluationDomain<F>,
) -> DensePolynomial<F> {
    let evals = sparse_matrix_by_vec(m, z);
    DensePolynomial::from_coefficients_vec(domain.ifft(&evals))
}

fn random_matrix_polynomial_evaluations<F: PrimeField>(
    m: &Matrix<F>,
    powers_of_r: &Vec<F>,
) -> Vec<F> {
    m.iter()
        .zip(powers_of_r.iter())
        .map(|(row, r_x)| *r_x * row.iter().map(|(v, _)| v).sum::<F>())
        .collect::<Vec<F>>()
}

fn aurora_setup<F: PrimeField, PCS: PolynomialCommitment<F, DensePolynomial<F>>>(
    r1cs: &ConstraintSystem<F>,
    rng: &mut impl RngCore,
) -> Result<(PCS::CommitterKey, PCS::VerifierKey), PCS::Error> {
    assert!(
        is_padded(&r1cs),
        "Received ConstraintSystem is nod padded. Please call pad_r1cs(cs) first."
    );

    if 1 << F::TWO_ADICITY < r1cs.num_constraints {
        panic!(
            "The field F has 2-Sylow subgroup of order 2^{}, but the R1CS requires 2^{}",
            F::TWO_ADICITY,
            log2(r1cs.num_constraints)
        );
    }

    let pp = PCS::setup(r1cs.num_constraints - 1, None, rng).unwrap();

    // No hiding needed, as this version of Aurora is not zero-knowledge
    PCS::trim(
        &pp,
        r1cs.num_constraints - 1,
        0,
        Some(&[r1cs.num_constraints - 1]),
    )
}

fn absorb_matrix<F: PrimeField + Absorb>(
    m: &Matrix<F>,
    sponge: &mut impl CryptographicSponge,
    label: &str,
) {
    sponge.absorb(&label.as_bytes());

    // Implementing domain separation to prevent collisions e.g. of the matrices
    // 0 0 0                0 0 0
    // 0 1 0       and      0 0 0
    // 0 0 0                0 1 0

    m.iter().enumerate().for_each(|(i, row)| {
        sponge.absorb(&format!("row_{i}").as_bytes());
        row.iter().for_each(|(v, i)| {
            sponge.absorb(v);
            sponge.absorb(i);
        });
    });
}

fn absorb_public_parameters<F, PCS>(
    vk: &PCS::VerifierKey,
    matrices: &ConstraintMatrices<F>,
    sponge: &mut impl CryptographicSponge,
) where
    F: PrimeField + Absorb,
    PCS: PolynomialCommitment<F, DensePolynomial<F>>,
{
    let ConstraintMatrices {
        a,
        b,
        c,
        num_instance_variables,
        num_witness_variables,
        ..
    } = matrices;
    sponge.absorb(&"Aurora".as_bytes());
    // TODO bound PCS::VerifierKey: Absorb, implement it for Ligero
    //    sponge.absorb(vk);
    sponge.absorb(&num_instance_variables);
    sponge.absorb(&num_witness_variables);
    absorb_matrix(&a, sponge, "A");
    absorb_matrix(&b, sponge, "B");
    absorb_matrix(&c, sponge, "C");
}

fn label_polynomials<F: PrimeField>(
    polynomials_and_labels: &[(&str, &DensePolynomial<F>)],
) -> Vec<LabeledPolynomial<F, DensePolynomial<F>>> {
    polynomials_and_labels
        .iter()
        .cloned()
        .map(|(label, polynomial)| {
            LabeledPolynomial::new(label.to_string(), polynomial.clone(), None, None)
        })
        .collect()
}

fn aurora_prove<F, PCS>(
    ck: &PCS::CommitterKey,
    vk: &PCS::VerifierKey,
    r1cs: &ConstraintSystem<F>,
    sponge: &mut impl CryptographicSponge,
) -> AuroraProof<F, PCS>
where
    F: PrimeField + Absorb,
    PCS: PolynomialCommitment<F, DensePolynomial<F>>,
{
    assert!(
        is_padded(&r1cs),
        "Received ConstraintSystem is nod padded. Please call pad_r1cs(r1cs) first."
    );

    let matrices = r1cs.to_matrices().unwrap();

    // 0. Initialising sponge with public parameters
    absorb_public_parameters::<F, PCS>(&vk, &matrices, sponge);

    let ConstraintMatrices {
        a,
        b,
        c,
        num_constraints: n,
        ..
    } = matrices;

    // 1. Constructing committed polynomials
    // Following the notation of the paper
    let h = GeneralEvaluationDomain::new(n).unwrap();

    let solution = [
        r1cs.instance_assignment.clone(),
        r1cs.witness_assignment.clone(),
    ]
    .concat();

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

    let zero_padded_witness = [
        vec![F::ZERO; r1cs.num_instance_variables],
        r1cs.witness_assignment.clone(),
    ]
    .concat();

    // Return the unique polynomial of degree < n that interpolates the given
    // values over h
    let h_interpolate = |evals: &Vec<F>| DensePolynomial::from_coefficients_vec(h.ifft(&evals));

    // Numerator
    let z_minus_v_star = h_interpolate(&zero_padded_witness);

    // TODO: Is there a more efficient way to compute this?
    // Denominator v_h_in = (x - 1) * (x - zeta^1) * ... * (x - zeta^(k-1))
    let v_h_in = h
        .elements()
        .take(r1cs.num_instance_variables) // 1, zeta, ..., zeta^(k-1)
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

    AuroraProof {
        commitments: coms,
        proof,
        evals: labeled_polynomials
            .iter()
            .map(|lp| lp.polynomial().evaluate(&a_point))
            .collect(),
    }
}

fn aurora_verify<F, PCS>(
    vk: &PCS::VerifierKey,
    aurora_proof: AuroraProof<F, PCS>,
    r1cs: &ConstraintSystem<F>,
    sponge: &mut impl CryptographicSponge,
) -> bool
where
    F: PrimeField + Absorb,
    PCS: PolynomialCommitment<F, DensePolynomial<F>>,
{
    assert!(
        is_padded(&r1cs),
        "Received ConstraintSystem is nod padded. Please call pad_r1cs(r1cs) first."
    );

    let matrices = r1cs.to_matrices().unwrap();

    // 0. Initialising sponge with public parameters
    absorb_public_parameters::<F, PCS>(vk, &matrices, sponge);

    let ConstraintMatrices {
        a,
        b,
        c,
        num_constraints: n,
        ..
    } = matrices;

    let AuroraProof {
        commitments: com,
        proof,
        evals,
    } = aurora_proof;

    // Absorb the first 5 commitments
    sponge.absorb(&com.iter().take(5).collect::<Vec<_>>());

    let r: F = sponge.squeeze_field_elements(1)[0];

    // ======================== Verify the proof ========================

    // Absorb the missing commitments to g1, g2
    sponge.absorb(&com.iter().skip(5).collect::<Vec<_>>());

    let a_point: F = sponge.squeeze_field_elements(1)[0];

    if !PCS::check(vk, &com, &a_point, evals.clone(), &proof, sponge, None).unwrap() {
        return false;
    }

    // ======================== Zero test ========================

    // Evaluations of the committed polynomials at a_point
    let [f_a_a, f_b_a, f_c_a, f_0_a, f_w_a, g_1_a, g_2_a] = evals[..] else {
        return false;
    };

    let h = GeneralEvaluationDomain::<F>::new(n).unwrap();

    let v_h_a = h.evaluate_vanishing_polynomial(a_point);

    if f_a_a * f_b_a - f_c_a != f_0_a * v_h_a {
        return false;
    }

    // ======================== Univariate sumcheck test ========================
    let zero_padded_instance = [
        r1cs.instance_assignment.clone(),
        vec![F::ZERO; r1cs.num_witness_variables],
    ]
    .concat();

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
        .take(r1cs.num_instance_variables)
        .map(|c| a_point - c)
        .product();

    let f_z_a = f_w_a * v_h_in_a + v_star_a;

    // Computing [1, r, r^2, ... r^(n-1)]
    let powers_of_r = powers(r, n);
    let p_r_a = h_evaluate_interpolator(&powers_of_r);

    let q_ar_a = h_evaluate_interpolator(&random_matrix_polynomial_evaluations(&a, &powers_of_r));
    let q_br_a = h_evaluate_interpolator(&random_matrix_polynomial_evaluations(&b, &powers_of_r));
    let q_cr_a = h_evaluate_interpolator(&random_matrix_polynomial_evaluations(&c, &powers_of_r));

    let r_pow_n = r * powers_of_r[n - 1];

    let u_a = (p_r_a * f_a_a - q_ar_a * f_z_a)
        + (p_r_a * f_b_a - q_br_a * f_z_a) * r_pow_n
        + (p_r_a * f_c_a - q_cr_a * f_z_a) * (r_pow_n * r_pow_n);

    u_a == g_1_a * v_h_a + g_2_a * a_point
}

fn inner_product<F: PrimeField>(v1: &[F], v2: &[F]) -> F {
    v1.iter().zip(v2).map(|(li, ri)| *li * ri).sum()
}
