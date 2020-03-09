pub mod adaptor;
pub mod cs;
// pub mod generator;
// pub mod prover;
// pub mod verifier;
// pub mod tester;
pub mod polynomials;
pub mod domains;
pub mod fft;
pub mod utils;
pub mod transparent_engine;

pub mod redshift;

pub mod plonk;

pub mod commitments;

pub mod better_cs;

pub use self::better_cs::adaptor::{TranspilationVariant, Transpiler, Adaptor, AdaptorCircuit};
pub use self::better_cs::keys::{SetupPolynomials, SetupPolynomialsPrecomputations, VerificationKey, Proof};

use crate::pairing::Engine;
use crate::{SynthesisError, Circuit};
use crate::multicore::Worker;
use self::better_cs::cs::PlonkCsWidth4WithNextStepParams;

pub fn transpile<E: Engine, C: crate::Circuit<E>>(circuit: C) -> Result<Vec<(usize, TranspilationVariant)>, SynthesisError> {
    let mut transpiler = Transpiler::<E, PlonkCsWidth4WithNextStepParams>::new();

    circuit.synthesize(&mut transpiler).expect("sythesize into traspilation must succeed");

    let hints = transpiler.into_hints();

    Ok(hints)
}

pub fn is_satisfied<E: Engine, C: crate::Circuit<E>>(
    circuit: C,
    hints: &Vec<(usize, TranspilationVariant)>
) -> Result<(), SynthesisError> {
    use crate::plonk::better_cs::cs::Circuit;

    let adapted_curcuit = AdaptorCircuit::<E, PlonkCsWidth4WithNextStepParams, _>::new(circuit, &hints);

    let mut assembly = self::better_cs::test_assembly::TestAssembly::new();

    adapted_curcuit.synthesize(&mut assembly)
}

pub fn setup<E: Engine, C: crate::Circuit<E>>(
    circuit: C,
    hints: &Vec<(usize, TranspilationVariant)>
) -> Result<SetupPolynomials<E, PlonkCsWidth4WithNextStepParams>, SynthesisError> {
    use crate::plonk::better_cs::cs::Circuit;

    let adapted_curcuit = AdaptorCircuit::<E, PlonkCsWidth4WithNextStepParams, _>::new(circuit, &hints);

    let mut assembly = self::better_cs::generator::GeneratorAssembly::<E, PlonkCsWidth4WithNextStepParams>::new();

    adapted_curcuit.synthesize(&mut assembly)?;
    assembly.finalize();

    let worker = Worker::new();

    assembly.setup(&worker)
}