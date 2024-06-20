use ark_crypto_primitives::sponge::{Absorb, CryptographicSponge};
use ark_ff::{PrimeField, Zero};
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain,
};
use ark_relations::r1cs::{ConstraintSystem, LinearCombination, Matrix};
use ark_std::cmp::max;
use ark_poly_commit::PolynomialCommitment;

use crate::utils::{powers, sparse_matrix_by_vec};

// TODO add reference to appendix B

struct AuroraProof<F, PCS>
where
    F: PrimeField + Absorb,
    PCS: PolynomialCommitment<F, DensePolynomial<F>>
{
    com_f_a: PCS::Commitment,
    com_f_b: PCS::Commitment,
    com_f_c: PCS::Commitment,
    com_f_0: PCS::Commitment,
    com_f_w: PCS::Commitment,
    com_g_1: PCS::Commitment,
    com_g_2: PCS::Commitment,
}

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

fn random_matrix_polynomial<F: PrimeField>(
    m: &Matrix<F>,
    r: F,
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

fn aurora_prove<F, PCS>
(
    r1cs: &ConstraintSystem<F>,
    sponge: &mut impl CryptographicSponge,
)
where
    F: PrimeField + Absorb,
    PCS: PolynomialCommitment<F, DensePolynomial<F>>,
{
    // TODO sanity checks, padding?
    assert!(
        is_padded(&r1cs),
        "Received ConstraintSystem is nod padded. Please call pad_r1cs(r1cs) first."
    );

    let matrices = r1cs.to_matrices().unwrap();

    let a = matrices.a;
    let b = matrices.b;
    let c = matrices.c;

    // 0. Initialising sponge with public parameters
    sponge.absorb(&"Aurora".as_bytes());
    sponge.absorb(&r1cs.num_instance_variables);
    sponge.absorb(&r1cs.num_witness_variables);
    absorb_matrix(&a, sponge, "A");
    absorb_matrix(&b, sponge, "B");
    absorb_matrix(&c, sponge, "C");

    // 1. Constructing committed polynomials
    // Following the notation of the paper
    let n = r1cs.num_constraints; // = num_instance variables + num_witness_variables if padded
    let h = GeneralEvaluationDomain::new(n).unwrap();
    // h_in = h^(n/k)
    let h_in = GeneralEvaluationDomain::new(r1cs.num_instance_variables).unwrap();

    let mut solution = r1cs.instance_assignment.clone();
    solution.extend(r1cs.witness_assignment.clone());

    // Note we can't compute f_a * f_b using an iFFT
    let f_a = matrix_polynomial(&a, &solution, &h);
    let f_b = matrix_polynomial(&b, &solution, &h);
    let f_c = matrix_polynomial(&c, &solution, &h);

    // Constructing v_h = x^n - 1
    let v_h = DensePolynomial::from(h.vanishing_polynomial());
    
    // Computing f_0 = (f_a * f_b - f_c) / v_h
    let f_0 = &(&(&f_a * &f_b) - &f_c) / &v_h;

    // TODO think about whether there is a more efficient way to compute this
    let v = DensePolynomial::from_coefficients_vec(h_in.ifft(&r1cs.instance_assignment));
    
    let v_h_in = DensePolynomial::from(h_in.vanishing_polynomial());

    let f_w = DensePolynomial::<F>::zero(); // TODO Confirm with Giacomo

    // commit to f_a, f_b, f_c, f_0,        f_w
    // degrees   <n   <n   <n   < n - 1     ??

    
    // Randomising polinomial through a squeezed challenge
    let r: F = sponge.squeeze_field_elements(1)[0];

    // 3: Univariate sumcheck
    let f_z = &f_w * &v_h_in + v;

    // Computing [1, r, r^2, ... r^(n-1)]
    let powers_of_r = powers(r, n);
    let p_r = DensePolynomial::from_coefficients_vec(h.ifft(&powers_of_r));
    
    let q_ar = random_matrix_polynomial(&a, r, &h);
    let q_br = random_matrix_polynomial(&b, r, &h);
    let q_cr = random_matrix_polynomial(&c, r, &h);
    
    let u =                 &(&(&p_r * &f_a) - &(&q_ar * &f_z)) +
            r.pow(n)      * &(&(&p_r * &f_b) - &(&q_br * &f_z)) +
            r.pow(2 * n)  * &(&(&p_r * &f_c) - &(&q_cr * &f_z));

}

// TODO verifier: check degrees of committed polynomials!

#[cfg(test)]
mod tests {
    use crate::{aurora::pad_r1cs, reader::read_constraint_system, TEST_DATA_PATH};
    use ark_bn254::Fr;
    use ark_ff::PrimeField;
    use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
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
        //                  ------- ins ------ | - wit -
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

    #[test]
    fn test_fft_consistency() {
        let n = 1 << 8;
        let k = 1 << 3;

        let h = GeneralEvaluationDomain::<Fr>::new(n).unwrap();
        let h_in = GeneralEvaluationDomain::<Fr>::new(k).unwrap();

        assert_eq!(h_in.elements().into_iter().nth(1), h.elements().into_iter().nth(1 << 5));
    }
}
