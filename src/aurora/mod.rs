use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain,
};
use ark_relations::r1cs::{ConstraintSystem, LinearCombination, Matrix};
use ark_std::cmp::max;

use crate::utils::{poly_div, poly_mul, sparse_matrix_by_vec};

// TODO add reference to appendix B

pub(crate) fn is_padded<F: PrimeField>(r1cs: &ConstraintSystem<F>) -> bool {
    let sol_len = r1cs.num_instance_variables + r1cs.num_witness_variables;
    r1cs.num_instance_variables.is_power_of_two()
        && sol_len.is_power_of_two()
        && sol_len == r1cs.num_constraints
}

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
        r1cs.witness_assignment.resize(padded_len, F::ZERO);
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

    // TODO Other unclear fields:
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

    // TODO think about whether there is a more efficient way to compute this
    let mut v_coeffs = r1cs.instance_assignment.clone();
    v_coeffs.resize(solution.len(), F::ZERO);
}

#[cfg(test)]
mod tests {
    use crate::{aurora::pad_r1cs, reader::read_constraint_system, TEST_DATA_PATH};
    use ark_bn254::Fr;
    use ark_ff::PrimeField;
    use ark_std::vec;

    fn to_sparse<F: PrimeField + From<i64>>(matrix: &Vec<Vec<i64>>) -> Vec<Vec<(F, usize)>> {
        matrix
            .iter()
            .map(|row| {
                row.iter()
                    .enumerate()
                    .filter_map(|(j, &coeff)| {
                        if coeff == 0 {
                            None
                        } else {
                            Some((F::from(coeff), j))
                        }
                    })
                    .collect::<Vec<(F, usize)>>()
            })
            .collect()
    }

    fn compare_matrices<F: PrimeField>(a: &Vec<Vec<(F, usize)>>, b: &Vec<Vec<(F, usize)>>) {
        a.iter().zip(b.iter()).for_each(|(row_a, row_b)| {
            row_a
                .iter()
                .zip(row_b.iter())
                .for_each(|((coeff_a, j_a), (coeff_b, j_b))| {
                    assert_eq!(coeff_a, coeff_b);
                    assert_eq!(j_a, j_b);
                });
        });
    }

    #[test]
    fn test_pad() {
        // - Original instance length: 5 -> Padded to 8
        // - Original witness length: 2 -> Padded to 8
        // - Smallest power of 2 geq 8 + 2 -> 16
        // - Original number of constraints: 4 -> 16

        let r1cs = read_constraint_system::<Fr>(
            &format!(TEST_DATA_PATH!(), "padding_test.r1cs"),
            &format!(TEST_DATA_PATH!(), "padding_test.wasm"),
        );

        let mut padded_r1cs = r1cs.clone();

        pad_r1cs(&mut padded_r1cs);

        println!(
            "Instance length {} -> {}",
            r1cs.num_instance_variables, padded_r1cs.num_instance_variables
        );
        println!(
            "Witness length {} -> {}",
            r1cs.num_witness_variables, padded_r1cs.num_witness_variables
        );
        println!(
            "Smallest power of 2 geq {} + {} -> {}",
            padded_r1cs.num_instance_variables,
            r1cs.num_witness_variables,
            padded_r1cs.num_constraints
        );
        println!(
            "Number of constraints: {} -> {}",
            r1cs.num_constraints, padded_r1cs.num_constraints
        );

        assert_eq!(padded_r1cs.num_instance_variables, 8);
        assert_eq!(padded_r1cs.num_witness_variables, 8);
        assert_eq!(padded_r1cs.num_constraints, 16);

        let matrices = r1cs.to_matrices().unwrap();

        let expected_a = vec![
            vec![0, -1, 0, 0, 0, 0, 0],
            vec![0, 0, 0, -1, 0, 0, 0],
            vec![0, 0, -1, 0, 0, 0, 0],
            vec![0, 0, 0, 0, -1, 0, 0],
        ];

        let expected_b = vec![
            vec![0, 1, 0, 0, 0, 0, 0],
            vec![0, 0, 0, 1, 0, 0, 0],
            vec![0, 0, 0, 0, 0, 1, 0],
            vec![0, 0, 0, 0, 0, 0, 1],
        ];

        let expected_c = vec![
            vec![0, 0, -1, 0, 0, 0, 0],
            vec![0, 0, 0, 0, -1, 0, 0],
            vec![0, 0, 0, 0, 0, 0, -1],
            vec![-42, 0, 0, 0, 0, 0, 0],
        ];

        // Solution vector: (1, a1, a2, b1, b2 | c, a2c)
        //                   ------ ins ------ | - wit -
        //
        // R1CS:
        // A*z  (·) B*z = C*z
        // -a1   *  a1  = -a2
        // -b1   *  b1  = -b2
        // -a2   *  c   = -a2c
        // -b2   *  a2c = -42

        compare_matrices(&matrices.a, &to_sparse(&expected_a));
        compare_matrices(&matrices.b, &to_sparse(&expected_b));
        compare_matrices(&matrices.c, &to_sparse(&expected_c));

        let padded_matrices = padded_r1cs.to_matrices().unwrap();

        // Padding matrices by hand. We want to chech that the columns of zeros
        // corresponding to the instance padding are really fit in between the
        // original instance- and witness-related colunns.
        let expected_padded_a = [
            vec![
                [vec![0, -1, 0, 0, 0], vec![0; 3], vec![0, 0], vec![0; 6]].concat(),
                [vec![0, 0, 0, -1, 0], vec![0; 3], vec![0, 0], vec![0; 6]].concat(),
                [vec![0, 0, -1, 0, 0], vec![0; 3], vec![0, 0], vec![0; 6]].concat(),
                [vec![0, 0, 0, 0, -1], vec![0; 3], vec![0, 0], vec![0; 6]].concat(),
            ],
            vec![vec![0; 16]; 12],
        ]
        .concat();

        let expected_padded_b = [
            vec![
                [vec![0, 1, 0, 0, 0], vec![0; 3], vec![0, 0], vec![0; 6]].concat(),
                [vec![0, 0, 0, 1, 0], vec![0; 3], vec![0, 0], vec![0; 6]].concat(),
                [vec![0, 0, 0, 0, 0], vec![0; 3], vec![1, 0], vec![0; 6]].concat(),
                [vec![0, 0, 0, 0, 0], vec![0; 3], vec![0, 1], vec![0; 6]].concat(),
            ],
            vec![vec![0; 16]; 12],
        ]
        .concat();

        let expected_padded_c = [
            vec![
                [vec![0, 0, -1, 0, 0], vec![0; 3], vec![0, 0], vec![0; 6]].concat(),
                [vec![0, 0, 0, 0, -1], vec![0; 3], vec![0, 0], vec![0; 6]].concat(),
                [vec![0, 0, 0, 0, 0], vec![0; 3], vec![0, -1], vec![0; 6]].concat(),
                [vec![-42, 0, 0, 0, 0], vec![0; 3], vec![0, 0], vec![0; 6]].concat(),
            ],
            vec![vec![0; 16]; 12],
        ]
        .concat();

        compare_matrices(&padded_matrices.a, &to_sparse(&expected_padded_a));
        compare_matrices(&padded_matrices.b, &to_sparse(&expected_padded_b));
        compare_matrices(&padded_matrices.c, &to_sparse(&expected_padded_c));
    }
}
