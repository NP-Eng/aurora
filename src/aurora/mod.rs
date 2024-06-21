use ark_std::{collections::HashMap, hash::Hash};

use ark_crypto_primitives::sponge::{Absorb, CryptographicSponge};
use ark_ff::PrimeField;
use ark_poly::{
    univariate::{DensePolynomial, SparsePolynomial},
    DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain, Polynomial,
};
use ark_poly_commit::{LabeledCommitment, LabeledPolynomial, PolynomialCommitment};
use ark_relations::r1cs::{ConstraintSystem, LinearCombination, Matrix};
use ark_std::cmp::max;

use crate::utils::{powers, sparse_matrix_by_vec};

// TODO add reference to appendix B

struct AuroraProof<F, PCS>
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
    powers_of_r: &Vec<F>,
    domain: &GeneralEvaluationDomain<F>,
) -> DensePolynomial<F> {
    let evals = m
        .iter()
        .enumerate()
        .map(|(i, row)| row.iter().map(|(v, _)| v).sum::<F>() * powers_of_r[i])
        .collect::<Vec<F>>();
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

fn aurora_prove<F, PCS>(
    ck: &PCS::CommitterKey,
    r1cs: &ConstraintSystem<F>,
    sponge: &mut impl CryptographicSponge,
) -> AuroraProof<F, PCS>
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

    let mut solution = r1cs.instance_assignment.clone();
    solution.extend(r1cs.witness_assignment.clone());

    // ======================== Computation of f_0 ========================

    // Note we can't compute f_a * f_b using an iFFT
    let f_a = matrix_polynomial(&a, &solution, &h);
    let f_b = matrix_polynomial(&b, &solution, &h);
    let f_c = matrix_polynomial(&c, &solution, &h);

    // Constructing v_h = x^n - 1
    let v_h = DensePolynomial::from(h.vanishing_polynomial());

    // Computing f_0 = (f_a * f_b - f_c) / v_h
    let f_0 = &(&(&f_a * &f_b) - &f_c) / &v_h;

    // ======================== Computation of f_w ========================

    let zero_padded_witness = [
        vec![F::ZERO; r1cs.num_instance_variables],
        r1cs.witness_assignment.clone(),
    ]
    .concat();

    let z_sub_v_star = DensePolynomial::from_coefficients_vec(h.ifft(&zero_padded_witness));

    // TODO: Is there a more efficient way to compute this?
    let v_h_in = (0..r1cs.num_instance_variables)
        .zip(h.elements().into_iter())
        .map(|(i, zeta)| vec![(i, zeta), (0, -F::ONE)])
        .map(SparsePolynomial::from_coefficients_vec)
        .map(DensePolynomial::from)
        .reduce(|acc, p| &acc * &p)
        .unwrap();

    let f_w = &z_sub_v_star / &v_h_in;

    // commit to f_a, f_b, f_c, f_0,        f_w
    // degrees   <n   <n   <n   < n - 1     ??

    // Randomising polinomial through a squeezed challenge
    let r: F = sponge.squeeze_field_elements(1)[0];

    // ======================== Computation of f_z ========================

    let zero_padded_instance = [
        r1cs.instance_assignment.clone(),
        vec![F::ZERO; r1cs.num_witness_variables],
    ]
    .concat();

    let v_star = DensePolynomial::from_coefficients_vec(h.ifft(&zero_padded_instance));

    // 3: Univariate sumcheck
    let f_z = &f_w * &v_h_in + v_star;

    // ======================== Computation of g_1, g_2 ========================

    // Computing [1, r, r^2, ... r^(n-1)]
    let powers_of_r = powers(r, n);
    let p_r = DensePolynomial::from_coefficients_vec(h.ifft(&powers_of_r));

    let q_ar = random_matrix_polynomial(&a, &powers_of_r, &h);
    let q_br = random_matrix_polynomial(&b, &powers_of_r, &h);
    let q_cr = random_matrix_polynomial(&c, &powers_of_r, &h);

    // TODO consider adding assert/error check before that n (the number of
    // rows/cols fits into a u64)
    let r_pow_n = r.pow([n as u64]);

    let u = (&(&p_r * &f_a) - &(&q_ar * &f_z))
        + &(&(&p_r * &f_b) - &(&q_br * &f_z)) * r_pow_n
        + &(&(&p_r * &f_c) - &(&q_cr * &f_z)) * (r_pow_n * r_pow_n);

    // R Euclidean domain
    // gamma, alpha, beta fixed
    // alpha, beta coprime
    // gamma = alpha * x + beta * y
    // Find x_0, y_0 such that 1 = gcd(alpha, beta) = alpha * x_0 + beta * y_0
    // Have solution (gamma * x_0, gamma * y_0)

    // In this case, we need to find x_0, y_0 such that 1 = v_h * x_0 + x * y_0
    // v_h = x^n - 1
    // x_0 = -1, y_0 = x^(n - 1)

    // alpha = -1 * u
    // beta = x^(n - 1) * u

    let g_1 = -u.clone();
    let g_2 = &DensePolynomial::from(SparsePolynomial::from_coefficients_vec(vec![(
        n - 1,
        F::ONE,
    )])) * &u;

    // TODO remove
    assert_eq!(
        u,
        &v_h * &g_1
            + &g_2
                * &DensePolynomial::from(SparsePolynomial::from_coefficients_vec(vec![(
                    1,
                    F::ONE
                )]))
    );

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

    let a: F = sponge.squeeze_field_elements(1)[0];

    let proof = PCS::open(
        ck,
        &labeled_polynomials,
        &com,
        &a,
        sponge,
        &com_states,
        None,
    )
    .unwrap();

    return AuroraProof {
        commitments: com,
        proof: proof,
        evals: labeled_poly_map
            .iter()
            .map(|(label, polynomial)| (label.to_string(), polynomial.evaluate(&r)))
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
    // TODO sanity checks, padding?
    assert!(
        is_padded(&r1cs),
        "Received ConstraintSystem is nod padded. Please call pad_r1cs(r1cs) first."
    );

    let matrices = r1cs.to_matrices().unwrap();
    let n = r1cs.num_constraints;

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

    let point: F = sponge.squeeze_field_elements(1)[0];

    if !PCS::check(vk, &com, &point, values, &proof, sponge, None).unwrap() {
        return false;
    }

    // ======================== Zero test ========================

    let v_h_in = (0..r1cs.num_instance_variables)
        .zip(
            GeneralEvaluationDomain::new(r1cs.num_instance_variables)
                .unwrap()
                .elements()
                .into_iter(),
        )
        .map(|(i, zeta)| vec![(i, zeta), (0, -F::ONE)])
        .map(SparsePolynomial::from_coefficients_vec)
        .map(DensePolynomial::from)
        .reduce(|acc, p| &acc * &p)
        .unwrap();

    if *evals.get("f_a").unwrap() * *evals.get("f_b").unwrap() - evals.get("f_c").unwrap()
        != *evals.get("f_0").unwrap() * v_h_in.evaluate(&point)
    {
        return false;
    }

    // ======================== Univariate sumcheck test ========================

    let h = GeneralEvaluationDomain::new(n).unwrap();

    let zero_padded_instance = [
        r1cs.instance_assignment.clone(),
        vec![F::ZERO; r1cs.num_witness_variables],
    ]
    .concat();

    let v_star = DensePolynomial::from_coefficients_vec(h.ifft(&zero_padded_instance));

    let f_z = *evals.get("f_w").unwrap() * v_h_in.evaluate(&point) + v_star.evaluate(&point);

    // Computing [1, r, r^2, ... r^(n-1)]
    let powers_of_r = powers(r, n);
    let p_r = DensePolynomial::from_coefficients_vec(h.ifft(&powers_of_r)).evaluate(&point);

    let q_ar = random_matrix_polynomial(&a, &powers_of_r, &h).evaluate(&point);
    let q_br = random_matrix_polynomial(&b, &powers_of_r, &h).evaluate(&point);
    let q_cr = random_matrix_polynomial(&c, &powers_of_r, &h).evaluate(&point);

    // TODO consider adding assert/error check before that n (the number of
    // rows/cols fits into a u64)
    let r_pow_n = r.pow([n as u64]);

    let u = (p_r * evals.get("f_a").unwrap() - q_ar * f_z)
        + (p_r * evals.get("f_b").unwrap() - q_br * f_z) * r_pow_n
        + (p_r * evals.get("f_c").unwrap() - q_cr * f_z) * (r_pow_n * r_pow_n);

    let v_h = DensePolynomial::from(h.vanishing_polynomial());

    if u != *evals.get("g_1").unwrap() * v_h.evaluate(&point) + *evals.get("g_2").unwrap() * point {
        return false;
    }

    true
}

#[cfg(test)]
mod tests {
    use crate::{aurora::pad_r1cs, reader::read_constraint_system, TEST_DATA_PATH};
    use ark_bn254::Fr;
    use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
    use ark_ff::PrimeField;
    use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
    use ark_poly_commit::{test_sponge, TestUVLigero};
    use ark_std::{
        rand::{Rng, RngCore},
        test_rng, vec,
    };

    use super::*;

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

        assert_eq!(
            h_in.elements().into_iter().nth(1),
            h.elements().into_iter().nth(1 << 5)
        );
    }

    #[test]
    fn test_prove() {
        let r1cs = read_constraint_system::<Fr>(
            &format!(TEST_DATA_PATH!(), "padding_test.r1cs"),
            &format!(TEST_DATA_PATH!(), "padding_test.wasm"),
        );

        let pp = TestUVLigero::<Fr>::setup(10, None, &mut test_rng()).unwrap();

        let (ck, vk) = TestUVLigero::<Fr>::trim(&pp, 0, 0, None).unwrap();

        let mut padded_r1cs = r1cs.clone();

        pad_r1cs(&mut padded_r1cs);

        let sponge: PoseidonSponge<Fr> = test_sponge();

        let aurora_proof =
            aurora_prove::<Fr, TestUVLigero<Fr>>(&ck, &padded_r1cs, &mut sponge.clone());

        assert!(aurora_verify::<Fr, TestUVLigero<Fr>>(
            &vk,
            aurora_proof,
            &padded_r1cs,
            &mut sponge.clone()
        ));
    }
}
