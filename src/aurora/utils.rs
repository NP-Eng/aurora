use std::cmp::max;

use ark_crypto_primitives::sponge::{Absorb, CryptographicSponge};
use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain,
};
use ark_poly_commit::{LabeledPolynomial, PolynomialCommitment};
use ark_relations::r1cs::{ConstraintMatrices, ConstraintSystem, LinearCombination, Matrix};

pub(crate) fn sparse_matrix_by_vec<F: PrimeField>(m: &Matrix<F>, z: &Vec<F>) -> Vec<F> {
    let mut res = vec![];
    for row in m {
        let mut row_res = F::ZERO;
        for (coeff, var) in row {
            row_res += *coeff * z[*var];
        }
        res.push(row_res);
    }
    res
}

pub(crate) fn powers<F: PrimeField>(r: F, n: usize) -> Vec<F> {
    let mut powers_of_r = vec![F::ONE];
    let mut last = F::ONE;
    (0..n).for_each(|_| {
        last *= r;
        powers_of_r.push(last);
    });
    powers_of_r
}

pub(crate) fn matrix_polynomial<F: PrimeField>(
    m: &Matrix<F>,
    z: &Vec<F>,
    domain: &GeneralEvaluationDomain<F>,
) -> DensePolynomial<F> {
    let evals = sparse_matrix_by_vec(m, z);
    DensePolynomial::from_coefficients_vec(domain.ifft(&evals))
}

pub(crate) fn random_matrix_polynomial_evaluations<F: PrimeField>(
    m: &Matrix<F>,
    powers_of_r: &Vec<F>,
) -> Vec<F> {
    m.iter()
        .zip(powers_of_r.iter())
        .map(|(row, r_x)| *r_x * row.iter().map(|(v, _)| v).sum::<F>())
        .collect::<Vec<F>>()
}

pub(crate) fn absorb_matrix<F: PrimeField + Absorb>(
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

pub(crate) fn absorb_public_parameters<F, PCS>(
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

pub(crate) fn label_polynomials<F: PrimeField>(
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

pub(crate) fn inner_product<F: PrimeField>(v1: &[F], v2: &[F]) -> F {
    v1.iter().zip(v2).map(|(li, ri)| *li * ri).sum()
}

pub(crate) fn is_padded<F: PrimeField>(r1cs: &ConstraintSystem<F>) -> bool {
    let sol_len = r1cs.num_instance_variables + r1cs.num_witness_variables;
    r1cs.num_instance_variables.is_power_of_two()
        && sol_len.is_power_of_two()
        && sol_len == r1cs.num_constraints
}

pub(crate) fn assert_padded<F: PrimeField>(r1cs: &ConstraintSystem<F>) {
    assert!(
        is_padded(r1cs),
        "Received ConstraintSystem is nod padded. Please call pad_r1cs(r1cs) first."
    );
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
