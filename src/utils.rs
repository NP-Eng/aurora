use ark_ff::PrimeField;
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, Polynomial};
use ark_relations::r1cs::Matrix;

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

pub(crate) fn poly_mul<F: PrimeField>(
    a: &DensePolynomial<F>,
    b: &DensePolynomial<F>,
) -> DensePolynomial<F> {
    let mut res = vec![F::ZERO; a.coeffs.len() + b.coeffs.len() - 1];

    for (i, a_coeff) in a.coeffs.iter().enumerate() {
        for (j, b_coeff) in b.coeffs.iter().enumerate() {
            res[i + j] += *a_coeff * *b_coeff;
        }
    }

    DensePolynomial::from_coefficients_vec(res)
}

pub(crate) fn poly_div<F: PrimeField>(
    a: &DensePolynomial<F>,
    b: &DensePolynomial<F>,
) -> (DensePolynomial<F>, DensePolynomial<F>) {
    // TODO copilot-generated, check
    let mut a = a;
    let mut b = b;
    let mut q = vec![F::ZERO; a.coeffs.len() - b.coeffs.len() + 1];

    while a.degree() >= b.degree() {
        let mut t = vec![F::ZERO; a.coeffs.len() - b.coeffs.len() + 1];
        t[a.degree() - b.degree()] = a.coeffs[a.degree()] / b.coeffs[b.degree()];
        let t = DensePolynomial::from_coefficients_vec(t);
        q[a.degree() - b.degree()] = t.coeffs[t.degree()];
        //a = a - (&t * b);
    }

    (DensePolynomial::from_coefficients_vec(q), a.clone())
}
