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
    use ark_ff::Field;

    use super::*;
    use crate::TEST_DATA_PATH;

    #[test]
    fn test_read_multiplication_r1cs() {
        // A, B, C
        // Each row is a constraint
        // Each column is a variable (1, instance entry or witness entry)

        // A = (0, 0, -1, 0)
        // B = (0, 0, 0, 1)
        // C = (0, -1, 0, 0)

        // z = (1, inst, wit) such that
        // Az (·) Bz = Cz

        // z = (1, i_1), (w_1, w_2)

        // Az_1 = (0, 0, -1, 0) * ((1, i_1), (w_1, w_2) = -w_1
        // Bz_1 = (0, 0, 0, 1) * ((1, i_1), (w_1, w_2) = w_2
        // Cz_1 = (0, -1, 0, 0) * ((1, i_1), (w_1, w_2) = -i_1

        // P claims: (-w_1) * w_2 = -i_1

        let r1cs = read_constraint_system::<Fr>(
            &format!(TEST_DATA_PATH!(), "multiplication.r1cs"),
            &format!(TEST_DATA_PATH!(), "multiplication.wasm")
        );
        
        let matrices = r1cs.to_matrices().unwrap();

        // A = (0, 0, -1, 0)
        assert!(matrices.a == vec![vec![(-Fr::ONE, 2)]]);
        
        // B = (0, 0, 0, 1)
        assert!(matrices.b == vec![vec![(Fr::ONE, 3)]]);
        
        // C = (0, -1, 0, 0)
        assert!(matrices.c == vec![vec![(-Fr::ONE, 1)]]);
    }

    #[test]
    fn test_read_sum_of_sqrts_r1cs() { 
        let r1cs = read_constraint_system::<Fr>(
            &format!(TEST_DATA_PATH!(), "sum_of_sqrt.r1cs"),
            &format!(TEST_DATA_PATH!(), "sum_of_sqrt.wasm")
        );

        // println!("Read RC1S:\n{r1cs:?}");
        
        // let matrices = r1cs.to_matrices().unwrap();

        // println!("A:\n{}", matrices.a.iter().map(|row| format!("{row:?}")).join("\n\t"));
        // println!("B:\n{}", matrices.b.iter().map(|row| format!("{row:?}")).join("\n\t"));
        // println!("C:\n{}", matrices.c.iter().map(|row| format!("{row:?}")).join("\n\t"));

        // assert!(matrices.a == vec![vec![(-Fr::ONE, 2)]]);
        // assert!(matrices.b == vec![vec![(Fr::ONE, 3)]]);
        // assert!(matrices.c == vec![vec![(-Fr::ONE, 1)]]);
    }
}
