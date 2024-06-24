use crate::{aurora::pad_r1cs, reader::read_constraint_system, TEST_DATA_PATH};
use ark_bn254::Fr;
use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
use ark_ff::{Field, PrimeField};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_poly_commit::{test_sponge, TestUVLigero};
use ark_std::{test_rng, vec};

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
        padded_r1cs.num_instance_variables, r1cs.num_witness_variables, padded_r1cs.num_constraints
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
    // Let v = (1, a1, a2, b1, b2) denote the instance vetor and
    // w = (c, a2c) the witness vector, both referring to the unpadded R1CS.
    // Then the circuit constrains the following:
    //   - a2 = a1^2
    //   - b2 = b1^2
    //   - a2c = a2 * c
    //   - 42 = b2 * a2c

    // Chosen solution:
    // v = (1, 3, 9, 17, 289)
    // w = (c, a2c) with
    //  - c = 42 * (b^2 * a^2)^(-1)
    //  - a2c = 9 * c

    let mut r1cs = read_constraint_system::<Fr>(
        &format!(TEST_DATA_PATH!(), "padding_test.r1cs"),
        &format!(TEST_DATA_PATH!(), "padding_test.wasm"),
    );

    // Instance: (1, a1, a2, b1, b2)
    let sol_c = Fr::from(42) * Fr::from(9 * 289).inverse().unwrap();
    let sol_a2c = Fr::from(9) * sol_c;
    r1cs.instance_assignment = vec![
        Fr::ONE,
        Fr::from(3),
        Fr::from(9),
        Fr::from(17),
        Fr::from(289),
    ];
    r1cs.witness_assignment = vec![sol_c, sol_a2c];

    assert!(r1cs.is_satisfied().unwrap());

    let mut padded_r1cs = r1cs.clone();

    pad_r1cs(&mut padded_r1cs);

    let sponge: PoseidonSponge<Fr> = test_sponge();

    let (ck, vk) = aurora_setup::<Fr, TestUVLigero<Fr>>(&padded_r1cs, &mut test_rng()).unwrap();

    let aurora_proof =
        aurora_prove::<Fr, TestUVLigero<Fr>>(&ck, &vk, &padded_r1cs, &mut sponge.clone());

    assert!(aurora_verify::<Fr, TestUVLigero<Fr>>(
        &vk,
        aurora_proof,
        &padded_r1cs,
        &mut sponge.clone()
    ));
}
