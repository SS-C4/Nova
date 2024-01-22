//! We execute a configurable number of iterations of the `sha256` function per step of Nova's recursion.
type G1 = pasta_curves::pallas::Point;
type Scalar = <G1 as Group>::Scalar;
type G2 = pasta_curves::vesta::Point;
use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum, num::Num, 
    ConstraintSystem, 
    SynthesisError
  };
use ff::Field;
use flate2::{write::ZlibEncoder, Compression};
use nova_snark::{
  traits::{
    circuit::{StepCircuit, TrivialCircuit},
    Group, ROCircuitTrait
  },
  provider::poseidon::{ PoseidonROCircuit, PoseidonConstantsCircuit },
  gadgets::utils::le_bits_to_num,
  CompressedSNARK, PublicParams, RecursiveSNARK,
};
use std::time::Instant;
use std::env;

use bellpepper::gadgets::{ sha256::sha256 as sha256, Assignment };
use sha2::{ Digest, Sha256 };
use std::marker::PhantomData;
use criterion::*;

const IS_PACKED: bool = true;

// #[derive(Clone, Debug)]
// struct Sha256Circuit<Scalar: PrimeField> {
//     preimage: Vec<u8>,
//     _p: PhantomData<Scalar>,
//   }

// impl <Scalar: PrimeField + PrimeFieldBits> Sha256Circuit<Scalar> {
//     pub fn new(preimage: Vec<u8>) -> Self {
//         Self {
//             preimage,
//             _p: PhantomData,
//         }
//     }
// }

// impl<Scalar: PrimeField + PrimeFieldBits> StepCircuit<Scalar> for Sha256Circuit<Scalar> {
//     fn arity(&self) -> usize {
//         1
//     }

//     fn synthesize<CS: ConstraintSystem<Scalar>>(
//         &self,
//         cs: &mut CS,
//         _z: &[AllocatedNum<Scalar>],
//     ) -> Result<Vec<AllocatedNum<Scalar>>, SynthesisError> {
//         let mut z_out: Vec<AllocatedNum<Scalar>> = Vec::new();

//         let bit_values: Vec<_> = self
//         .preimage
//         .clone()
//         .into_iter()
//         .flat_map(|byte| (0..8).map(move |i| (byte >> i) & 1u8 == 1u8))
//         .map(Some)
//         .collect();
//         assert_eq!(bit_values.len(), self.preimage.len() * 8);

//         let preimage_bits = bit_values
//         .into_iter()
//         .enumerate()
//         .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("preimage bit {i}")), b))
//         .map(|b| b.map(Boolean::from))
//         .collect::<Result<Vec<_>, _>>()?;

//         let hash_bits = sha256(cs.namespace(|| "sha256"), &preimage_bits)?;

//         for (i, hash_bits) in hash_bits.chunks(256_usize).enumerate() {
//             let mut num = Num::<Scalar>::zero();
//             let mut coeff = Scalar::ONE;
//             for bit in hash_bits {
//                 num = num.add_bool_with_coeff(CS::one(), bit, coeff);

//                 coeff = coeff.double();
//             }

//             let hash = AllocatedNum::alloc(cs.namespace(|| format!("input {i}")), || {
//                 Ok(*num.get_value().get()?)
//             })?;

//             // num * 1 = hash
//             cs.enforce(
//                 || format!("packing constraint {i}"),
//                 |_| num.lc(Scalar::ONE),
//                 |lc| lc + CS::one(),
//                 |lc| lc + hash.get_variable(),
//             );
//             z_out.push(hash);
//         }

//         // sanity check with the hasher
//         let mut hasher = Sha256::new();
//         hasher.update(&self.preimage);
//         let hash_result = hasher.finalize();

//         let mut s = hash_result
//         .iter()
//         .flat_map(|&byte| (0..8).rev().map(move |i| (byte >> i) & 1u8 == 1u8));

//         for b in hash_bits {
//             match b {
//                 Boolean::Is(b) => {
//                 assert!(s.next().unwrap() == b.get_value().unwrap());
//                 }
//                 Boolean::Not(b) => {
//                 assert!(s.next().unwrap() != b.get_value().unwrap());
//                 }
//                 Boolean::Constant(_b) => {
//                 panic!("Can't reach here")
//                 }
//             }
//         }

//         Ok(z_out)
//     }
// }


// Multiple sha256 circuits per step
#[derive(Clone, Debug)]
struct Sha256CircuitMultiple<Scalar> {
    iters: usize,
    preimage: Vec<Vec<u8>>,
    _p: PhantomData<Scalar>,
}

impl Sha256CircuitMultiple<Scalar> {
    pub fn new(iters: usize, preimage: Vec<Vec<u8>>) -> Self {
        Self {
            iters,
            preimage,
            _p: PhantomData,
        }
    }
}

impl StepCircuit<Scalar> for Sha256CircuitMultiple<Scalar> {
    fn arity(&self) -> usize {
        self.iters
    }

    fn synthesize<CS: ConstraintSystem<Scalar>>(
        &self,
        cs: &mut CS,
        _z: &[AllocatedNum<Scalar>],
      ) -> Result<Vec<AllocatedNum<Scalar>>, SynthesisError> {
        let mut z_out: Vec<AllocatedNum<Scalar>> = Vec::new();

        for j in 0..self.iters {
            let mut z_out_j = Vec::new();

            let bit_values = self
            .preimage[j]
            .clone()
            .into_iter()
            .flat_map(|byte| (0..8).map(move |i| (byte >> i) & 1u8 == 1u8))
            .map(Some)
            .collect::<Vec<_>>();
            assert_eq!(bit_values.len(), self.preimage[j].len() * 8);

            let preimage_bits = bit_values
            .into_iter()
            .enumerate()
            .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("preimage {j} bit {i}")), b))
            .map(|b| b.map(Boolean::from))
            .collect::<Result<Vec<_>, _>>()?;

            let hash_bits = sha256(cs.namespace(|| format!("sha256 {j}")), &preimage_bits)?;

            for (i, hash_bits) in hash_bits.chunks(256_usize).enumerate() {
                let mut num = Num::<Scalar>::zero();
                let mut coeff = Scalar::ONE;
                for bit in hash_bits {
                    num = num.add_bool_with_coeff(CS::one(), bit, coeff);

                    coeff = coeff.double();
                }

                let hash = AllocatedNum::alloc(cs.namespace(|| format!("input {j}/{i}")), || {
                    Ok(*num.get_value().get()?)
                })?;

                // num * 1 = hash
                cs.enforce(
                    || format!("packing constraint {j}/{i}"),
                    |_| num.lc(Scalar::ONE),
                    |lc| lc + CS::one(),
                    |lc| lc + hash.get_variable(),
                );

                z_out_j.push(hash);
            }
            
            z_out.extend_from_slice(&z_out_j);

            // sanity check with the hasher
            let mut hasher = Sha256::new();
            hasher.update(&self.preimage[j]);
            let hash_result = hasher.finalize();

            let mut s = hash_result
            .iter()
            .flat_map(|&byte| (0..8).rev().map(move |i| (byte >> i) & 1u8 == 1u8));

            for b in hash_bits {
                match b {
                    Boolean::Is(b) => {
                    assert!(s.next().unwrap() == b.get_value().unwrap());
                    }
                    Boolean::Not(b) => {
                    assert!(s.next().unwrap() != b.get_value().unwrap());
                    }
                    Boolean::Constant(_b) => {
                    panic!("Can't reach here")
                    }
                }
            }
        }

        if IS_PACKED == true {
          // Trying to create a new variable here and add constraint for it later

          // There are currently 34945 constraints in the circuit (including the extra one)
          // Add those many extra variables with value something - don't care about correctness for now

          // let num_constraints = 34944; // For num_copies_per_step = 1
          let num_constraints = 60074; // For num_copies_per_step = 2
          // let num_constraints = 85204; // For num_copies_per_step = 3
          // let num_constraints = 111888; // For num_copies_per_step = 4
          // let num_constraints = 137018; // For num_copies_per_step = 5
          // let num_constraints = 262668; // For num_copies_per_step = 10
          // let num_constraints = 515522; // For num_copies_per_step = 20
          // let num_constraints = 1021230; // For num_copies_per_step = 40

          for i in 0..num_constraints {
              let _ = AllocatedNum::alloc(
                cs.namespace(|| format!("poso_var_{}", i)), 
                || Ok(Scalar::from(445262))
              )?;
          }

          // Add new variables for PoSO outputs and bit decomposition
          // This should be 9 for PoSO outputs and 9 * 100 for bit decomposition
          for i in 0..9 {
              let _ = AllocatedNum::alloc(
                cs.namespace(|| format!("poso_out_{}", i)), 
                || Ok(Scalar::from(445262))
              )?;
          }
          for i in 0..900 {
              let _ = AllocatedNum::alloc(
                cs.namespace(|| format!("bit_decomp_{}", i)), 
                || Ok(Scalar::from(445262))
              )?;
          }

          // Should add a hash gadget here 
          // Takes input z_i and previous hash output as input
          let constants = PoseidonConstantsCircuit::<Scalar>::default();
          let num_absorbs = 2;
          let mut ro = PoseidonROCircuit::<Scalar>::new(constants.clone(), num_absorbs);

          ro.absorb(&z_out[0]);
          ro.absorb(&AllocatedNum::alloc(cs.namespace(|| "absorb"), || Ok(Scalar::from(547788)))?);

          let hash_bits = ro.squeeze(cs.namespace(|| "Extra hash"), 250).unwrap();
          let _ = le_bits_to_num(cs.namespace(|| "convert bits to num"), &hash_bits)?;
        }

        // // Should add a hash gadget here - dupe for baseline
        // // Takes input z_i and previous hash output as input
        // let constants = PoseidonConstantsCircuit::<Scalar>::default();
        // let num_absorbs = 2;
        // let mut ro = PoseidonROCircuit::<Scalar>::new(constants.clone(), num_absorbs);

        // ro.absorb(&z_out[0]);
        // ro.absorb(&AllocatedNum::alloc(cs.namespace(|| "absorb"), || Ok(Scalar::from(547788)))?);

        // let hash_bits = ro.squeeze(cs.namespace(|| "Extra hash"), 250).unwrap();
        // let _ = le_bits_to_num(cs.namespace(|| "convert bits to num"), &hash_bits)?;

        // Add extra constraint to use z_out - square it
        let y = z_out[0].clone();
        let x = y.square(cs.namespace(|| format!("x_sq_0")))?;

        // Enforce that y = z_out[0]^2
        cs.enforce(
            || format!("squaring constraint"),
            |lc| lc + y.get_variable(),
            |lc| lc + y.get_variable(),
            |lc| lc + x.get_variable(),
        );
        
        Ok(z_out)
    }
}

fn main() {
  println!("Nova for Sha256");
  println!("=========================================================");

  let args: Vec<String> = env::args().collect();
  println!("num_steps: {:?}, num_copies_per_step: {:?}", args[1], args[2]);
  println!("IS_PACKED: {:?}", IS_PACKED);

  let num_steps = args[1].parse::<usize>().unwrap();
  let num_copies_per_step = args[2].parse::<usize>().unwrap();
    
  let circuit_primary = Sha256CircuitMultiple::new(
      num_copies_per_step, 
      vec![vec![0u8; 1 << 4]; num_copies_per_step]
  );
  let circuit_secondary = TrivialCircuit::default();

  println!("Proving {num_copies_per_step} copies of Sha256 per step");

  // produce public parameters
  let start = Instant::now();
  println!("Producing public parameters...");
  let pp = PublicParams::<
    G1,
    G2,
    Sha256CircuitMultiple<<G1 as Group>::Scalar>,
    TrivialCircuit<<G2 as Group>::Scalar>,
  >::setup(&circuit_primary, &circuit_secondary);
  println!("PublicParams::setup, took {:?} ", start.elapsed());

  println!(
    "Number of constraints per step (primary circuit): {}",
    pp.num_constraints().0
  );
  println!(
    "Number of constraints per step (secondary circuit): {}",
    pp.num_constraints().1
  );

  println!(
    "Number of variables per step (primary circuit): {}",
    pp.num_variables().0
  );
  println!(
    "Number of variables per step (secondary circuit): {}",
    pp.num_variables().1
  );

  // println!(
  //   "R1CS A matrix: {:?}",
  //   pp.r1cs_shape().0
  // );

  let z0_primary = vec![<G1 as Group>::Scalar::from(0u64); num_copies_per_step];
  let z0_secondary = vec![<G2 as Group>::Scalar::from(1u64)];

  type C1 = Sha256CircuitMultiple<<G1 as Group>::Scalar>;
  type C2 = TrivialCircuit<<G2 as Group>::Scalar>;
  // produce a recursive SNARK
  println!("Generating a RecursiveSNARK...");
  let mut recursive_snark: RecursiveSNARK<G1, G2, C1, C2> = RecursiveSNARK::<G1, G2, C1, C2>::new(
    black_box(&pp),
    black_box(&circuit_primary),
    black_box(&circuit_secondary),
    black_box(z0_primary.clone()),
    black_box(z0_secondary.clone()),
  );

  for i in 0..num_steps {
    let start = Instant::now();
    let res = recursive_snark.prove_step(
      black_box(&pp),
      black_box(&circuit_primary),
      black_box(&circuit_secondary),
      black_box(z0_primary.clone()),
      black_box(z0_secondary.clone()),
    );
    // assert!(res.is_ok());
    println!(
      "RecursiveSNARK::prove_step {}: {:?}, took {:?} ",
      i,
      res.is_ok(),
      start.elapsed()
    );
  }

  // verify the recursive SNARK
  println!("Verifying a RecursiveSNARK...");
  let start = Instant::now();
  let res = recursive_snark.verify(&pp, num_steps, &z0_primary, &z0_secondary);
  println!(
    "RecursiveSNARK::verify: {:?}, took {:?}",
    res.is_ok(),
    start.elapsed()
  );
  // assert!(res.is_ok());

  // produce a compressed SNARK
  println!("Generating a CompressedSNARK using Spartan with IPA-PC...");
  let (pk, vk) = CompressedSNARK::<_, _, _, _, S1, S2>::setup(&pp).unwrap();

  let start = Instant::now();
  type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;
  type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<G2>;
  type S1 = nova_snark::spartan::snark::RelaxedR1CSSNARK<G1, EE1>;
  type S2 = nova_snark::spartan::snark::RelaxedR1CSSNARK<G2, EE2>;

  let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &pk, &recursive_snark);
  println!(
    "CompressedSNARK::prove: {:?}, took {:?}",
    res.is_ok(),
    start.elapsed()
  );
  assert!(res.is_ok());
  let compressed_snark = res.unwrap();

  let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
  bincode::serialize_into(&mut encoder, &compressed_snark).unwrap();
  let compressed_snark_encoded = encoder.finish().unwrap();
  println!(
    "CompressedSNARK::len {:?} bytes",
    compressed_snark_encoded.len()
  );

  // verify the compressed SNARK
  println!("Verifying a CompressedSNARK...");
  let start = Instant::now();
  let res = compressed_snark.verify(&vk, num_steps, z0_primary, z0_secondary);
  println!(
    "CompressedSNARK::verify: {:?}, took {:?}",
    res.is_ok(),
    start.elapsed()
  );
  assert!(res.is_ok());
  println!("=========================================================");
  
}
