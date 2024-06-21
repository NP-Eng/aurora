use ark_ff::PrimeField;
use ark_relations::r1cs::Matrix;

#[cfg(test)]
use ark_crypto_primitives::sponge::{
    poseidon::{PoseidonConfig, PoseidonSponge},
    CryptographicSponge,
};

#[cfg(test)]
use ark_std::test_rng;

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
