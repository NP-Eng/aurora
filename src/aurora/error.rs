use ark_ff::PrimeField;
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::PolynomialCommitment;
use ark_std::error::Error;
use core::fmt::{Debug, Display, Formatter, Result};

/// The error type for Aurora.
pub enum AuroraError<F, PCS>
where
    F: PrimeField,
    PCS: PolynomialCommitment<F, DensePolynomial<F>>,
{
    // The witness passed to `prove` does not match the (unpadded) witness
    // length of the R1CS
    IncorrectWitnessLength { received: usize, expected: usize },
    // Error of the associated PCS
    PCSError(PCS::Error),
}

impl<F, PCS> Debug for AuroraError<F, PCS>
where
    F: PrimeField,
    PCS: PolynomialCommitment<F, DensePolynomial<F>>,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        <Self as Display>::fmt(self, f)
    }
}

impl<F, PCS> Display for AuroraError<F, PCS>
where
    F: PrimeField,
    PCS: PolynomialCommitment<F, DensePolynomial<F>>,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            AuroraError::IncorrectWitnessLength { received, expected } => write!(
                f,
                "Incorrect (unpadded) witness length: received {}, expected {}",
                received, expected
            ),
            AuroraError::PCSError(e) => write!(f, "{}", e),
        }
    }
}

impl<F, PCS> Error for AuroraError<F, PCS>
where
    F: PrimeField,
    PCS: PolynomialCommitment<F, DensePolynomial<F>>,
{
}
