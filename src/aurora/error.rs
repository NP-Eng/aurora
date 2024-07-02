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
    // The number of evaluations contained in the proof does not match the
    // expected number
    IncorrectNumberOfEvaluations { received: usize, expected: usize },
    // The instance passed to `prove` does not match the instance
    // length of the R1CS
    IncorrectInstanceLength { received: usize, expected: usize },
    // The witness passed to `prove` does not match the witness
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
            AuroraError::IncorrectNumberOfEvaluations { received, expected } => write!(
                f,
                "Incorrect number of evaluations: received {}, expected {}",
                received, expected
            ),
            AuroraError::IncorrectInstanceLength { received, expected } => write!(
                f,
                "Incorrect (unpadded) instance length: received {}, expected {}",
                received, expected
            ),
            AuroraError::IncorrectWitnessLength { received, expected } => write!(
                f,
                "Incorrect witness length: received {}, expected {}",
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
