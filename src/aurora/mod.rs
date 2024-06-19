use ark_poly::{Polynomial, univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain};
use ark_std::cmp::max;
use ark_ff::PrimeField;
use ark_relations::r1cs::{ConstraintSystem, Matrix};

use crate::utils::{poly_div, poly_mul, sparse_matrix_by_vec};

// TODO add reference to appendix B

fn is_padded<F: PrimeField>(r1cs: &ConstraintSystem<F>) -> bool {
    let sol_len = r1cs.num_instance_variables + r1cs.num_witness_variables;
    sol_len == r1cs.num_constraints && sol_len.is_power_of_two()
}

fn pad_r1cs<F: PrimeField>(r1cs: &mut ConstraintSystem<F>){
    let sol_len = r1cs.num_instance_variables + r1cs.num_witness_variables;
    
    let padded_len = max(sol_len, r1cs.num_constraints).next_power_of_two();
    
    if sol_len == padded_len && r1cs.num_constraints == padded_len {
        return;
    }

    let sol_pad = padded_len - sol_len;
    let constraint_pad = padded_len - r1cs.num_constraints;

    r1cs.num_witness_variables += sol_pad;
    r1cs.num_constraints += constraint_pad;
    r1cs.witness_assignment.resize(padded_len, F::ZERO);
    
    // TODO What to do about linear combinations? I think they have no place in
    // Aurora: we want plain (A, B, C)-defined R1CSs
    // Related ConstraintSystem fields:
    //  - pub num_linear_combinations: usize,
    //  - lc_map: BTreeMap<LcIndex, LinearCombination<F>>,
    //  - a_constraints: Vec<LcIndex>,
    //  - b_constraints: Vec<LcIndex>,
    //  - c_constraints: Vec<LcIndex>,
    //  - lc_assignment_cache: Rc<RefCell<BTreeMap<LcIndex, F>>>,

    // TODO Other unclear fields:
    //  - pub cache_map: Rc<RefCell<BTreeMap<TypeId, Box<dyn Any>>>>,
    // - #[cfg(feature = "std")]
    //    constraint_traces: Vec<Option<ConstraintTrace>>,
}

fn matrix_polynomial<F: PrimeField>(m: &Matrix<F>, z: &Vec<F>, domain: &GeneralEvaluationDomain<F>) -> DensePolynomial<F> {
    let evals = sparse_matrix_by_vec(m, z);
    DensePolynomial::from_coefficients_vec(domain.ifft(&evals))
}

fn aurora_setup<F: PrimeField>(r1cs: ConstraintSystem<F>) {
    assert!(
        is_padded(&r1cs),
        "Received ConstraintSystem is nod padded. Please call pad_r1cs(cs) first."
    );

    if 1 << F::TWO_ADICITY > r1cs.num_constraints {
        panic!("Number of constraints must be a power of 2.");
    }

    // TODO Setup PCS here once we are generic over it
}

fn aurora_prove<F: PrimeField>(r1cs: ConstraintSystem<F>) {
    
    // TODO sanity checks, padding?

    let matrices = r1cs.to_matrices().unwrap();

    let a = matrices.a;
    let b = matrices.b;
    let c = matrices.c;

    // Following the notation of the paper
    let n = r1cs.num_constraints; // = num_instance variables + num_witness_variables if padded
    let h = GeneralEvaluationDomain::new(n).unwrap();

    let mut solution = r1cs.instance_assignment.clone();
    solution.extend(r1cs.witness_assignment.clone());

    // Note we can't compute f_a * f_b using an iFFT

    let f_a = matrix_polynomial(&a, &solution, &h);
    let f_b = matrix_polynomial(&b, &solution, &h);
    let f_c = matrix_polynomial(&c, &solution, &h);
    
    // Constructing v_h = x^n - 1
    let mut v_h_coeffs = vec![F::ZERO; n + 1];
    v_h_coeffs[0] = -F::ONE;
    v_h_coeffs[n] = F::ONE;
    let v_h = DensePolynomial::from_coefficients_vec(v_h_coeffs);

    // Computing f_0 = (f_a * f_b - f_c) / v_h
    let f_0 = poly_div(&(&poly_mul(&f_a, &f_b) - &f_c), &v_h);
}
