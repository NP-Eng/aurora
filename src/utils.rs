use ark_ff::PrimeField;
use ark_relations::r1cs::Matrix;

#[cfg(test)]
use ark_crypto_primitives::sponge::{poseidon::{PoseidonConfig, PoseidonSponge}, CryptographicSponge};

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

#[cfg(test)]
pub(crate) fn test_sponge<F: PrimeField>() -> PoseidonSponge<F> {
    let full_rounds = 8;
    let partial_rounds = 31;
    let alpha = 17;

    let mds = vec![
        vec![F::one(), F::zero(), F::one()],
        vec![F::one(), F::one(), F::zero()],
        vec![F::zero(), F::one(), F::one()],
    ];

    let mut v = Vec::new();
    let mut ark_rng = test_rng();

    for _ in 0..(full_rounds + partial_rounds) {
        let mut res = Vec::new();

        for _ in 0..3 {
            res.push(F::rand(&mut ark_rng));
        }
        v.push(res);
    }
    let config = PoseidonConfig::new(full_rounds, partial_rounds, alpha, mds, v, 2, 1);
    PoseidonSponge::new(&config)
}