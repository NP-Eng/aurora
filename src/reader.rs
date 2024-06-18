use ark_std::path::Path;
use ark_circom::{CircomBuilder, CircomConfig};
use ark_ff::PrimeField;
use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};

fn read_constraint_system<F: PrimeField>(r1cs_file: impl AsRef<Path>, wasm_file: impl AsRef<Path>) -> ConstraintSystem<F> {
    // Load the WASM and R1CS for witness and proof generation
    let cfg = CircomConfig::<F>::new(
        wasm_file, r1cs_file
    ).unwrap();

    // Insert our public inputs as key value pairs
    let builder = CircomBuilder::new(cfg);
    let circom = builder.build().unwrap();
    let cs = ConstraintSystem::<F>::new_ref();
    circom.generate_constraints(cs.clone()).unwrap();
    cs.into_inner().unwrap()
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use ark_bn254::Fr;

    use super::*;
    use crate::TEST_DATA_PATH;

    #[test]
    fn test_read_matrices() {
        let r1cs = read_constraint_system::<Fr>(
            &format!(TEST_DATA_PATH!(), "circuit.r1cs"),
            &format!(TEST_DATA_PATH!(), "circuit.wasm")
        );

        println!("Read RC1S:\n{r1cs:?}");
        
        let matrices = r1cs.to_matrices().unwrap();

        println!("A:\n{}", matrices.a.iter().map(|row| format!("{row:?}")).join("\n\t"));
        println!("B:\n{}", matrices.b.iter().map(|row| format!("{row:?}")).join("\n\t"));
        println!("C:\n{}", matrices.c.iter().map(|row| format!("{row:?}")).join("\n\t"));
    }
}
