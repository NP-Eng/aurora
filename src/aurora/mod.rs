use ark_std::{collections::HashMap, log2, rand::RngCore};

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
    evals: HashMap<String, F>,
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

fn random_matrix_polynomial<F: PrimeField>(
    m: &Matrix<F>,
    powers_of_r: &Vec<F>,
    domain: &GeneralEvaluationDomain<F>,
) -> DensePolynomial<F> {
    let evals = m
        .iter()
        .zip(powers_of_r.iter())
        .map(|(row, r_x)| *r_x * row.iter().map(|(v, _)| v).sum::<F>())
        .collect::<Vec<F>>();

    DensePolynomial::from_coefficients_vec(domain.ifft(&evals))
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
    // TODO check if generated matrices are deterministically ordered, otherwise
    // sort them here
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

    // Numerator
    let z_minus_v_star = DensePolynomial::from_coefficients_vec(h.ifft(&zero_padded_witness));

    // TODO: Is there a more efficient way to compute this?
    // Denominator v_h_in = (x - 1) * (x - zeta^1) * ... * (x - zeta^(k-1))
    let v_h_in = h
        .elements()
        .take(r1cs.num_instance_variables) // 1, zeta, ..., zeta^(k-1)
        .map(|c| vec![(1, F::ONE), (0, -c)]) // x - zeta^i
        .map(SparsePolynomial::from_coefficients_vec)
        .map(DensePolynomial::from)
        .reduce(|acc, p| &acc * &p) // multiply together
        .unwrap();

    let f_w = &z_minus_v_star / &v_h_in;

    // commit to f_a, f_b, f_c, f_0,        f_w
    // degrees   <n   <n   <n   < n - 1     ??

    // ======================== Computation of f_z ========================

    let f_z = DensePolynomial::from_coefficients_vec(h.ifft(&solution));

    // ======================== Computation of g_1, g_2 ========================

    // Randomising polinomial through a squeezed challenge
    let r: F = sponge.squeeze_field_elements(1)[0];

    // Computing [1, r, r^2, ... r^(n-1)]
    let powers_of_r = powers(r, n);
    let p_r = DensePolynomial::from_coefficients_vec(h.ifft(&powers_of_r));

    let q_ar = random_matrix_polynomial(&a, &powers_of_r, &h);
    let q_br = random_matrix_polynomial(&b, &powers_of_r, &h);
    let q_cr = random_matrix_polynomial(&c, &powers_of_r, &h);

    // TODO consider adding assert/error check before that n (the number of
    // rows/cols fits into a u64)
    let r_pow_n = r * powers_of_r[n - 1];

    let u = (&(&p_r * &f_a) - &(&q_ar * &f_z))
        + &(&(&p_r * &f_b) - &(&q_br * &f_z)) * r_pow_n
        + &(&(&p_r * &f_c) - &(&q_cr * &f_z)) * (r_pow_n * r_pow_n);

    // We need to find x_0, y_0 such that 1 = v_h * x_0 + x * y_0 where
    // v_h = x^n - 1
    // x_0 = -1, y_0 = x^(n - 1)
    // We have the following immediate solution:
    // x_0 = -u
    // y_0 = x^(n - 1) * u

    let g_1 = -u.clone();
    let g_2 = &DensePolynomial::from(SparsePolynomial::from_coefficients_vec(vec![(
        n - 1,
        F::ONE,
    )])) * &u;

    //======================== PCS commitment/proof ========================

    let labeled_poly_map = vec![
        ("f_a", f_a),
        ("f_b", f_b),
        ("f_c", f_c),
        ("f_0", f_0),
        ("f_w", f_w),
        ("g_1", g_1),
        ("g_2", g_2),
    ]
    .iter()
    .cloned()
    .collect::<HashMap<_, _>>();

    let labeled_polynomials = labeled_poly_map
        .iter()
        .map(|(label, polynomial)| {
            LabeledPolynomial::new(label.to_string(), polynomial.clone(), None, None)
        })
        .collect::<Vec<_>>();

    let (com, com_states) = PCS::commit(ck, &labeled_polynomials, None).unwrap();

    sponge.absorb(&com);

    let a_point: F = sponge.squeeze_field_elements(1)[0];

    let proof = PCS::open(
        ck,
        &labeled_polynomials,
        &com,
        &a_point,
        sponge,
        &com_states,
        None,
    )
    .unwrap();

    return AuroraProof {
        commitments: com,
        proof,
        evals: labeled_poly_map
            .iter()
            .map(|(label, polynomial)| (label.to_string(), polynomial.evaluate(&a_point)))
            .collect::<HashMap<_, _>>(),
    };
}

// TODO verifier: check degrees of committed polynomials!
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

    let r: F = sponge.squeeze_field_elements(1)[0];

    // ======================== Verify the proof ========================

    let AuroraProof {
        commitments: com,
        proof,
        evals,
    } = aurora_proof;

    // Fetch the evaluations of the committed polynomials in the correct order
    let values = com
        .iter()
        .map(|c| *evals.get(c.label()).unwrap())
        .collect::<Vec<_>>();

    sponge.absorb(&com);

    let a_point: F = sponge.squeeze_field_elements(1)[0];

    // TODO make sure this is safe
    if !PCS::check(vk, &com, &a_point, values, &proof, sponge, None).unwrap() {
        return false;
    }

    // ======================== Zero test ========================

    let h = GeneralEvaluationDomain::<F>::new(n).unwrap();

    let v_h_a = a_point.pow([n as u64]) - F::ONE;

    if *evals.get("f_a").unwrap() * *evals.get("f_b").unwrap() - evals.get("f_c").unwrap()
        != *evals.get("f_0").unwrap() * v_h_a
    {
        return false;
    }

    // ======================== Univariate sumcheck test ========================
    let zero_padded_instance = [
        r1cs.instance_assignment.clone(),
        vec![F::ZERO; r1cs.num_witness_variables],
    ]
    .concat();

    let v_star = DensePolynomial::from_coefficients_vec(h.ifft(&zero_padded_instance));

    // TODO is there a better way to compute
    // - v_star(a_point)?
    // - p_r(a_point)?
    // - q_ar(a_point)?
    // - q_br(a_point)?
    // - q_cr(a_point)?
    // - v_h(a_point)?
    // f_0 = (f_a * f_b - f_c) / v_h

    let v_h_in = h
        .elements()
        .take(r1cs.num_instance_variables) // 1, zeta, ..., zeta^(k-1)
        .map(|c| vec![(1, F::ONE), (0, -c)]) // x - zeta^i
        .map(SparsePolynomial::from_coefficients_vec)
        .map(DensePolynomial::from)
        .reduce(|acc, p| &acc * &p) // multiply together
        .unwrap();

    let f_z_a = *evals.get("f_w").unwrap() * v_h_in.evaluate(&a_point) + v_star.evaluate(&a_point);

    // Computing [1, r, r^2, ... r^(n-1)]
    let powers_of_r = powers(r, n);
    let p_r_a = DensePolynomial::from_coefficients_vec(h.ifft(&powers_of_r)).evaluate(&a_point);

    // Computing [1, r, r^2, ... r^(n-1)]
    let q_ar_a = random_matrix_polynomial(&a, &powers_of_r, &h).evaluate(&a_point);
    let q_br_a = random_matrix_polynomial(&b, &powers_of_r, &h).evaluate(&a_point);
    let q_cr_a = random_matrix_polynomial(&c, &powers_of_r, &h).evaluate(&a_point);

    // TODO consider adding assert/error check before that n (the number of
    // rows/cols fits into a u64)
    let r_pow_n = r * powers_of_r[n - 1];

    let u_a = (p_r_a * evals.get("f_a").unwrap() - q_ar_a * f_z_a)
        + (p_r_a * evals.get("f_b").unwrap() - q_br_a * f_z_a) * r_pow_n
        + (p_r_a * evals.get("f_c").unwrap() - q_cr_a * f_z_a) * (r_pow_n * r_pow_n);

    u_a == *evals.get("g_1").unwrap() * v_h_a + *evals.get("g_2").unwrap() * a_point
}
