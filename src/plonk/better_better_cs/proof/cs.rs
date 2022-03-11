

use futures::executor::block_on;
use heavy_ops_service::{Worker as NewWorker, AsyncWorkManager};

use crate::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use crate::pairing::{Engine, CurveAffine, CurveProjective};
use crate::bit_vec::BitVec;

use crate::plonk::better_better_cs::utils::BinopAddAssignScaled;
use crate::{SynthesisError};
use std::marker::PhantomData;

use crate::worker::Worker;
use crate::plonk::domains::*;

pub use crate::plonk::cs::variable::*;
use crate::plonk::better_cs::utils::*;

use crate::plonk::fft::cooley_tukey_ntt::*;


use super::polynomials_new::*;
use super::setup::Setup;
// pub use crate::plonk::better_better_cs::gates::main_gate_with_d_next::*;
pub use crate::plonk::better_better_cs::proof::main_gate_with_d_next::Width4MainGateWithDNext;
pub use crate::plonk::better_better_cs::proof::main_gate_with_d_next_new::Width4MainGateWithDNextNew;
pub use crate::plonk::utils::*;
pub use crate::plonk::better_better_cs::utils::*;
pub use crate::plonk::better_better_cs::proof::lookup_tables::*;
// pub use crate::plonk::better_better_cs::proof::setup::*;
pub use crate::plonk::better_better_cs::proof::data_structures_new::*;



pub trait SynthesisMode: Clone + Send + Sync + std::fmt::Debug {
    const PRODUCE_WITNESS: bool;
    const PRODUCE_SETUP: bool;
}
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct SynthesisModeGenerateSetup;

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct SynthesisModeProve;

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct SynthesisModeTesting;

impl SynthesisMode for SynthesisModeGenerateSetup {
    const PRODUCE_WITNESS: bool = false;
    const PRODUCE_SETUP: bool = true;
}

impl SynthesisMode for SynthesisModeProve {
    const PRODUCE_WITNESS: bool = true;
    const PRODUCE_SETUP: bool = false;
}

impl SynthesisMode for SynthesisModeTesting {
    const PRODUCE_WITNESS: bool = true;
    const PRODUCE_SETUP: bool = true;
}

pub trait Circuit<E: Engine> {
    type MainGate: MainGate<E>;
    fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError>;
    fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
        Ok(
            vec![Self::MainGate::default().into_internal()]
        )
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum Coefficient {
    PlusOne,
    MinusOne,
    Other
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct PolynomialMultiplicativeTerm(pub Coefficient, pub Vec<PolynomialInConstraint>);

impl PolynomialMultiplicativeTerm {
    fn degree(&self) -> usize {
        self.1.len()
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub(crate) struct PolynomialOpeningRequest {
    pub(crate) id: PolyIdentifier,
    pub(crate) dilation: TimeDilation,
}

pub trait GateInternal<E: Engine>: Send 
    + Sync 
    + 'static 
    + std::any::Any 
    + std::fmt::Debug
{
    fn name(&self) -> &'static str;
    fn degree(&self) -> usize;
    fn can_include_public_inputs(&self) -> bool;
    fn all_queried_polynomials(&self) -> Vec<PolynomialInConstraint>;
    fn setup_polynomials(&self) -> Vec<PolyIdentifier>;
    fn variable_polynomials(&self) -> Vec<PolyIdentifier>;
    fn witness_polynomials(&self) -> Vec<PolyIdentifier> {
        vec![]
    }
    fn benefits_from_linearization(&self) -> bool;
    fn linearizes_over(&self) -> Vec<PolynomialInConstraint>;
    fn needs_opened_for_linearization(&self) -> Vec<PolynomialInConstraint>;
    fn num_quotient_terms(&self) -> usize;
    fn verify_on_row<'a>(&self, row: usize, poly_storage: &AssembledPolynomialStorage< E>, last_row: bool) -> E::Fr;
    fn contribute_into_quotient<'a, 'b>(
        &self, 
        domain_size: usize,
        poly_storage: &mut AssembledPolynomialStorage< E>,
        monomials_storage: &AssembledPolynomialStorageForMonomialForms<E>,
        challenges: &[E::Fr],
        omegas_bitreversed: &BitReversedOmegas<E::Fr>,
        omegas_inv_bitreversed: &OmegasInvBitreversed<E::Fr>,
        worker: &Worker
    ) -> Result<Polynomial<E::Fr, Values>, SynthesisError>;
    fn contribute_into_linearization<'a>(
        &self, 
        domain_size: usize,
        at: E::Fr,
        queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        monomials_storage: &AssembledPolynomialStorageForMonomialForms<E>,
        challenges: &[E::Fr],
        worker: &Worker
    ) -> Result<Polynomial<E::Fr, Coefficients>, SynthesisError>;
    fn contribute_into_verification_equation(
        &self, 
        domain_size: usize,
        at: E::Fr,
        queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        challenges: &[E::Fr],
    ) -> Result<E::Fr, SynthesisError>;
    fn put_public_inputs_into_selector_id(&self) -> Option<usize>;
    fn box_clone(&self) -> Box<dyn GateInternal<E>>;
    fn contribute_into_linearization_commitment(
        &self, 
        domain_size: usize,
        at: E::Fr,
        queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        commitments_storage: &std::collections::HashMap<PolyIdentifier, E::G1Affine>,
        challenges: &[E::Fr],
    ) -> Result<E::G1, SynthesisError>;
}

pub trait Gate<E: Engine>: GateInternal<E>
    + Sized
    + Clone
    + std::hash::Hash
    + std::default::Default 
{
    fn as_internal(&self) -> &dyn GateInternal<E> {
        self as &dyn GateInternal<E>
    }

    fn into_internal(self) -> Box<dyn GateInternal<E>> {
        Box::from(self) as Box<dyn GateInternal<E>>
    }
}

pub trait MainGate<E: Engine>: Gate<E> {
    const NUM_LINEAR_TERMS: usize;
    const NUM_VARIABLES: usize;
    const NUM_VARIABLES_ON_NEXT_STEP: usize;

    // fn num_linear_terms(&self) -> usize;
    // fn num_variables(&self) -> usize;
    // fn num_variables_of_next_step(&self) -> usize;

    fn range_of_multiplicative_term() -> std::ops::Range<usize>;
    fn range_of_linear_terms() -> std::ops::Range<usize>;
    fn index_for_constant_term() -> usize;
    fn range_of_next_step_linear_terms() -> std::ops::Range<usize>;
    fn format_term(instance: MainGateTerm<E>, padding: Variable) -> Result<(Vec<Variable>, Vec<E::Fr>), SynthesisError>;
    fn format_linear_term_with_duplicates(instance: MainGateTerm<E>, padding: Variable) -> Result<(Vec<Variable>, Vec<E::Fr>), SynthesisError>;
    fn dummy_vars_to_inscribe(dummy: Variable) -> Vec<Variable>;
    fn empty_coefficients() -> Vec<E::Fr>;
    fn contribute_into_quotient_for_public_inputs<'a, 'b>(
        &self, 
        domain_size: usize,
        public_inputs: &[E::Fr],
        poly_storage: &mut AssembledPolynomialStorage< E>,
        monomial_storage: & AssembledPolynomialStorageForMonomialForms<E>,
        challenges: &[E::Fr],
        omegas_bitreversed: &BitReversedOmegas<E::Fr>,
        omegas_inv_bitreversed: &OmegasInvBitreversed<E::Fr>,
        worker: &Worker
    ) -> Result<Polynomial<E::Fr, Values>, SynthesisError>;

    fn contribute_into_linearization_for_public_inputs<'a>(
        &self, 
        domain_size: usize,
        public_inputs: &[E::Fr],
        at: E::Fr,
        queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        monomials_storage: & AssembledPolynomialStorageForMonomialForms<E>,
        challenges: &[E::Fr],
        worker: &Worker
    ) -> Result<Polynomial<E::Fr, Coefficients>, SynthesisError>;
    
    fn add_inputs_into_quotient(
        &self, 
        domain_size: usize,
        public_inputs: &[E::Fr],
        at: E::Fr,
        challenges: &[E::Fr],
    ) -> Result<E::Fr, SynthesisError>;
    // fn contribute_into_verification_equation_for_public_inputs(
    //     &self, 
    //     domain_size: usize,
    //     public_inputs: &[E::Fr],
    //     at: E::Fr,
    //     queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
    //     challenges: &[E::Fr],
    // ) -> Result<E::Fr, SynthesisError>;
    fn contribute_into_linearization_commitment_for_public_inputs(
        &self, 
        domain_size: usize,
        public_inputs: &[E::Fr],
        at: E::Fr,
        queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        commitments_storage: &std::collections::HashMap<PolyIdentifier, E::G1Affine>,
        challenges: &[E::Fr],
    ) -> Result<E::G1, SynthesisError>;
}

impl<E: Engine> std::hash::Hash for dyn GateInternal<E> {
    fn hash<H>(&self, state: &mut H) where H: std::hash::Hasher {
        self.type_id().hash(state);
        self.name().hash(state);
        self.degree().hash(state);
    }
}

impl<E: Engine> PartialEq for dyn GateInternal<E> {
    fn eq(&self, other: &Self) -> bool {
        self.type_id() == other.type_id() &&
        self.name() == other.name() &&
        self.degree() == other.degree()
    }
}

impl<E: Engine> Eq for dyn GateInternal<E> {}

impl<E: Engine> Clone for Box<dyn GateInternal<E>> {
    fn clone(&self) -> Self {
        self.box_clone()
    }
}
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct LinearCombinationOfTerms(pub Vec<PolynomialMultiplicativeTerm>);

impl LinearCombinationOfTerms {
    fn terms(&self) -> &[PolynomialMultiplicativeTerm] {
       &self.0[..]
    }
}

#[derive(Clone, Debug)]
pub enum ArithmeticTerm<E: Engine>{
    Product(Vec<Variable>, E::Fr),
    SingleVariable(Variable, E::Fr),
    Constant(E::Fr),
}

impl<E: Engine> ArithmeticTerm<E> {
    pub fn from_variable(var: Variable) -> Self {
        ArithmeticTerm::SingleVariable(var, E::Fr::one())
    }

    pub fn from_variable_and_coeff(var: Variable, coeff: E::Fr) -> Self {
        ArithmeticTerm::SingleVariable(var, coeff)
    }

    pub fn constant(coeff: E::Fr) -> Self {
        ArithmeticTerm::Constant(coeff)
    }

    pub fn mul_by_variable(self, other: Variable) -> Self {
        match self {
            ArithmeticTerm::Product(mut terms, coeff) => {
                terms.push(other);

                ArithmeticTerm::Product(terms, coeff)
            },
            ArithmeticTerm::SingleVariable(this, coeff) => {
                let terms = vec![this, other];

                ArithmeticTerm::Product(terms, coeff)
            },
            ArithmeticTerm::Constant(coeff) => {
                let terms = vec![other];

                ArithmeticTerm::Product(terms, coeff)
            },
        }
    }

    pub fn scale(&mut self, by: &E::Fr) {
        match self {
            ArithmeticTerm::Product(_, ref mut coeff) => {
                coeff.mul_assign(by);
            },
            ArithmeticTerm::SingleVariable(_, ref mut coeff) => {
                coeff.mul_assign(by);
            },
            ArithmeticTerm::Constant(ref mut coeff) => {
                coeff.mul_assign(by);
            },
        }
    }
}

#[derive(Clone, Debug)]
pub struct MainGateTerm<E: Engine>{
    pub(crate) terms: Vec<ArithmeticTerm<E>>,
    pub(crate) vars_scratch: std::collections::HashMap<Variable, usize>,
    pub(crate) num_multiplicative_terms: usize,
    pub(crate) num_constant_terms: usize
}

impl<E: Engine> MainGateTerm<E> {
    pub fn new() -> Self {
        Self {
            terms: Vec::with_capacity(8),
            vars_scratch: std::collections::HashMap::with_capacity(8),
            num_multiplicative_terms: 0,
            num_constant_terms: 0
        }
    }

    pub fn len_without_constant(&self) -> usize {
        self.terms.len()
    }

    pub fn add_assign(&mut self, other: ArithmeticTerm<E>) {
        match other {
            ArithmeticTerm::Product(_, _) => {
                self.num_multiplicative_terms += 1;
                self.terms.push(other);
            },
            ArithmeticTerm::SingleVariable(var, coeff) => {
                // deduplicate 
                if self.vars_scratch.get(&var).is_some() {
                    let index = *self.vars_scratch.get(&var).unwrap();
                    match &mut self.terms[index] {
                        ArithmeticTerm::SingleVariable(_, ref mut c) => {
                            c.add_assign(&coeff);
                        },
                        _ => {
                            unreachable!()
                        }
                    }
                } else {
                    // just push
                    self.vars_scratch.insert(var, self.terms.len());
                    self.terms.push(other);
                }
            },
            ArithmeticTerm::Constant(_) => {
                self.num_constant_terms += 1;
                self.terms.push(other);
            },
        }
        
        debug_assert!(self.num_constant_terms <= 1, "must duplicate constants");        
    }

    pub fn add_assign_allowing_duplicates(&mut self, other: ArithmeticTerm<E>) {
        match other {
            ArithmeticTerm::Product(_, _) => {
                self.num_multiplicative_terms += 1;
                self.terms.push(other);
            },
            ArithmeticTerm::SingleVariable(_, _) => {
                // we just push and don't even count this variable as duplicatable
                self.terms.push(other);
            },
            ArithmeticTerm::Constant(_) => {
                self.num_constant_terms += 1;
                self.terms.push(other);
            },
        }
        
        debug_assert!(self.num_constant_terms <= 1, "must duplicate constants");        
    }

    pub fn sub_assign(&mut self, mut other: ArithmeticTerm<E>) {
        match &mut other {
            ArithmeticTerm::Product(_, ref mut coeff) => {
                coeff.negate();
            },
            ArithmeticTerm::SingleVariable(_, ref mut coeff) => {
                coeff.negate();
            },
            ArithmeticTerm::Constant(ref mut coeff) => {
                coeff.negate(); 
            },
        }

        self.add_assign(other);

        debug_assert!(self.num_constant_terms <= 1, "must not duplicate constants");        
    }

    pub fn sub_assign_allowing_duplicates(&mut self, mut other: ArithmeticTerm<E>) {
        match &mut other {
            ArithmeticTerm::Product(_, ref mut coeff) => {
                coeff.negate();
            },
            ArithmeticTerm::SingleVariable(_, ref mut coeff) => {
                coeff.negate();
            },
            ArithmeticTerm::Constant(ref mut coeff) => {
                coeff.negate(); 
            },
        }

        self.add_assign_allowing_duplicates(other);

        debug_assert!(self.num_constant_terms <= 1, "must not duplicate constants");        
    }
}

pub fn get_from_map_unchecked<E: Engine>(
    key_with_dilation: PolynomialInConstraint,
    ldes_map: &AssembledPolynomialStorage< E>
) -> &Polynomial<E::Fr, Values> {

    let (key, dilation_value) = key_with_dilation.into_id_and_raw_dilation();

    let r = if dilation_value == 0 {
        match key {
            k @ PolyIdentifier::VariablesPolynomial(..) => {
                ldes_map.state_map.get(&k).expect(&format!("Must get poly {:?} from ldes storage", &k))
            },
            k @ PolyIdentifier::WitnessPolynomial(..) => {
                ldes_map.witness_map.get(&k).expect(&format!("Must get poly {:?} from ldes storage", &k))
            },           
            k @ PolyIdentifier::GateSetupPolynomial(..) => {
                ldes_map.setup_map.get(&k).expect(&format!("Must get poly {:?} from ldes storage", &k))
            },
            _ => {
                unreachable!();
            }
        }
    } else {
        ldes_map.scratch_space.get(&key_with_dilation).expect(&format!("Must get poly {:?} from lde storage", &key_with_dilation))
    };

    r
}

// pub fn ensure_in_map_or_create<'a, 'b, E: Engine>(
//     key_with_dilation: PolynomialInConstraint,
//     domain_size: usize,
//     lde_factor: usize,
//     coset_factor: E::Fr,
//     monomials_map: & AssembledPolynomialStorageForMonomialForms<E>,
//     ldes_map: &mut AssembledPolynomialStorage< E>,
//     async_manager: Arc<AsyncWorkManager<E>>,
//     worker: NewWorker,
//     is_background: bool,
// ) -> Result<(), SynthesisError> {
//     block_on(ensure_in_map_or_create_async(
//         key_with_dilation,
//         domain_size,
//         lde_factor,
//         coset_factor,
//         monomials_map,
//         ldes_map,
//         async_manager,
//         worker,
//         is_background,
//     ))
// }

pub async fn ensure_in_map_or_create_async<'a, 'b, E: Engine>(
    key_with_dilation: PolynomialInConstraint,
    domain_size: usize,
    lde_factor: usize,
    coset_factor: E::Fr,
    monomials_map: & AssembledPolynomialStorageForMonomialForms<E>,
    ldes_map: &mut AssembledPolynomialStorage< E>,
    async_manager: Arc<AsyncWorkManager<E>>,
    worker: NewWorker,
    is_background: bool,
) -> Result<(), SynthesisError> {
    assert!(ldes_map.is_bitreversed);
    assert_eq!(ldes_map.lde_factor, lde_factor);

    let (key, dilation_value) = key_with_dilation.into_id_and_raw_dilation();

    let mut contains_in_scratch_or_maps = false;

    if dilation_value == 0 {
        match key {
            k @ PolyIdentifier::VariablesPolynomial(..) => {
                if ldes_map.state_map.get(&k).is_some() {
                    contains_in_scratch_or_maps = true;
                }
            },
            k @ PolyIdentifier::WitnessPolynomial(..) => {
                if ldes_map.witness_map.get(&k).is_some() {
                    contains_in_scratch_or_maps = true;
                }
            },           
            k @ PolyIdentifier::GateSetupPolynomial(..) => {
                if ldes_map.setup_map.get(&k).is_some() {
                    contains_in_scratch_or_maps = true;
                }
            },
            _ => {
                unreachable!();
            }
        }
    } else {
        if ldes_map.scratch_space.get(&key_with_dilation).is_some() {
            contains_in_scratch_or_maps = true;
        }
    };

    if !contains_in_scratch_or_maps {
        // optimistic case: we have already calculated value without dilation
        // but now need to just rotate
        let lde_without_dilation = match key {
            k @ PolyIdentifier::VariablesPolynomial(..) => {
                ldes_map.state_map.get(&k)
            },
            k @ PolyIdentifier::WitnessPolynomial(..) => {
                ldes_map.witness_map.get(&k)
            },           
            k @ PolyIdentifier::GateSetupPolynomial(..) => {
                ldes_map.setup_map.get(&k)
            },
            _ => {
                unreachable!();
            }
        };

        let mut done = false;

        let rotated = if let Some(lde) = lde_without_dilation.as_ref() {
            let rotation_factor = dilation_value * lde_factor;
            let f = lde.clone_shifted_assuming_bitreversed(rotation_factor, worker.child(), false).await?;
            drop(lde);

            Some(f)
        } else {
            None
        };

        drop(lde_without_dilation);

        if let Some(f) = rotated {
            // let proxy = PolynomialProxy::from_owned(f);
            ldes_map.scratch_space.insert(key_with_dilation, f);

            done = true;
        };

        if !done {
            // perform LDE and push

            let monomial = match key {
                k @ PolyIdentifier::VariablesPolynomial(..) => {
                    monomials_map.state_map.get(&k).unwrap()
                },
                k @ PolyIdentifier::WitnessPolynomial(..) => {
                    monomials_map.witness_map.get(&k).unwrap()
                },           
                k @ PolyIdentifier::GateSetupPolynomial(..) => {
                    monomials_map.setup_map.get(&k).unwrap()
                },
                _ => {
                    unreachable!();
                }
            };
        
            // let lde = monomial.clone().bitreversed_lde_using_bitreversed_ntt(
            //     &worker, 
            //     lde_factor, 
            //     omegas_bitreversed, 
            //     &coset_factor
            // )?;
            let lde_values = async_manager.coset_lde(monomial.arc_coeffs(), lde_factor, &coset_factor, worker.child(), is_background).await;
            let lde = Polynomial::from_values(lde_values).unwrap();
        
            let final_lde = if dilation_value != 0 {
                let rotation_factor = dilation_value * lde_factor;
                let f = lde.clone_shifted_assuming_bitreversed(rotation_factor, worker.child(), false).await?;
                drop(lde);
        
                f
            } else {
                lde
            };

            // insert back

            // let proxy = PolynomialProxy::from_owned(final_lde);

            if dilation_value == 0 {
                match key {
                    k @ PolyIdentifier::VariablesPolynomial(..) => {
                        ldes_map.state_map.insert(k, final_lde);
                    },
                    k @ PolyIdentifier::WitnessPolynomial(..) => {
                        ldes_map.witness_map.insert(k, final_lde);
                    },           
                    k @ PolyIdentifier::GateSetupPolynomial(..) => {
                        ldes_map.setup_map.insert(k, final_lde);
                    },
                    _ => {
                        unreachable!();
                    }
                }
            } else {
                ldes_map.scratch_space.insert(key_with_dilation, final_lde);
            };

            done = true;
        }

        assert!(done);
    }

    Ok(())
}

pub(crate) struct SimpleBitmap(u64, usize);

impl SimpleBitmap {
    pub(crate) fn new() -> Self {
        Self(0u64, 0)
    }

    pub(crate) fn get_next_unused(&mut self) -> usize {
        for i in 0..64 {
            if self.get(i) == false {
                return i;
            }
        }

        unreachable!()
    }

    pub(crate) fn get(&self, idx: usize) -> bool {
        1u64 << idx & self.0 > 0
    }

    pub(crate) fn set(&mut self, idx: usize) {
        self.0 |= 1u64 << idx;
    }
}

pub trait PlonkConstraintSystemParams<E: Engine>: Sized + Copy + Clone + Send + Sync {
    const STATE_WIDTH: usize;
    const WITNESS_WIDTH: usize;
    const HAS_WITNESS_POLYNOMIALS: bool;
    const HAS_CUSTOM_GATES: bool;
    const CAN_ACCESS_NEXT_TRACE_STEP: bool;
}

use std::sync::Arc;

pub trait ConstraintSystem<E: Engine> {
    type Params: PlonkConstraintSystemParams<E>;
    type MainGate: MainGate<E>;

    // allocate a variable
    fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>;

    // allocate an input variable
    fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>;

    fn new_single_gate_for_trace_step<G: Gate<E>>(&mut self, 
        equation: &G,
        coefficients_assignments: &[E::Fr],
        variables_assignments: &[Variable],
        witness_assignments: &[E::Fr]
    ) -> Result<(), SynthesisError> {
        self.begin_gates_batch_for_step()?;
        self.new_gate_in_batch(
            equation,
            coefficients_assignments,
            variables_assignments,
            witness_assignments
        )?;
        self.end_gates_batch_for_step()
    }

    fn get_main_gate(&self) -> &Self::MainGate;

    fn allocate_main_gate(&mut self, term: MainGateTerm<E>) -> Result<(), SynthesisError> {
        let (vars, coeffs) = Self::MainGate::format_term(term, Self::get_dummy_variable())?;

        let mg = Self::MainGate::default();

        self.new_single_gate_for_trace_step(
            &mg,
            &coeffs,
            &vars,
            &[]
        )
    }

    fn begin_gates_batch_for_step(&mut self) -> Result<(), SynthesisError>;
    fn new_gate_in_batch<G: Gate<E>>(&mut self, 
        equation: &G,
        coefficients_assignments: &[E::Fr],
        variables_assignments: &[Variable],
        witness_assignments: &[E::Fr]
    ) -> Result<(), SynthesisError>;
    fn end_gates_batch_for_step(&mut self) -> Result<(), SynthesisError>;

    fn allocate_variables_without_gate(&mut self, 
        variables_assignments: &[Variable],
        witness_assignments: &[E::Fr]
    ) -> Result<(), SynthesisError>;

    fn get_value(&self, _variable: Variable) -> Result<E::Fr, SynthesisError> { 
        Err(SynthesisError::AssignmentMissing)
    }

    fn get_dummy_variable() -> Variable;

    fn get_explicit_zero(&mut self) -> Result<Variable, SynthesisError>;
    fn get_explicit_one(&mut self) -> Result<Variable, SynthesisError>;

    fn add_table(&mut self, table: LookupTableApplication<E>) -> Result<Arc<LookupTableApplication<E>>, SynthesisError>;
    fn get_table(&self, functional_name: &str) -> Result<Arc<LookupTableApplication<E>>, SynthesisError>; 

    fn add_multitable(&mut self, table: MultiTableApplication<E>) -> Result<(), SynthesisError>;
    fn get_multitable(&self, functional_name: &str) -> Result<Arc<MultiTableApplication<E>>, SynthesisError>; 

    fn apply_single_lookup_gate(&mut self, variables: &[Variable], gate: Arc<LookupTableApplication<E>>) -> Result<(), SynthesisError>;
    fn apply_multi_lookup_gate(&mut self, variables: &[Variable], gate: Arc<MultiTableApplication<E>>) -> Result<(), SynthesisError>;

    fn get_current_step_number(&self) -> usize;
    fn get_current_aux_gate_number(&self) -> usize;
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct PlonkCsWidth4WithNextStepParams;
impl<E: Engine> PlonkConstraintSystemParams<E> for PlonkCsWidth4WithNextStepParams {
    const STATE_WIDTH: usize =  4;
    const WITNESS_WIDTH: usize = 0;
    const HAS_WITNESS_POLYNOMIALS: bool = false;
    const HAS_CUSTOM_GATES: bool =  false;
    const CAN_ACCESS_NEXT_TRACE_STEP: bool = true;
}

#[derive(Clone, Copy, Debug)]
pub struct PlonkCsWidth4WithNextStepAndCustomGatesParams;

impl<E: Engine> PlonkConstraintSystemParams<E> for PlonkCsWidth4WithNextStepAndCustomGatesParams {
    const STATE_WIDTH: usize =  4;
    const WITNESS_WIDTH: usize = 0;
    const HAS_WITNESS_POLYNOMIALS: bool = false;
    const HAS_CUSTOM_GATES: bool = true;
    const CAN_ACCESS_NEXT_TRACE_STEP: bool = true;
}

#[derive(Clone)]
pub struct PolynomialStorage<E: Engine> {
    pub state_map: std::collections::HashMap<PolyIdentifier, Vec<Variable>>,
    pub witness_map: std::collections::HashMap<PolyIdentifier, Vec<E::Fr>>,
    pub setup_map: std::collections::HashMap<PolyIdentifier, Vec<E::Fr>>,
}

impl<E: Engine> PolynomialStorage<E> {
    pub fn new() -> Self {
        Self {
            state_map: std::collections::HashMap::new(),
            witness_map: std::collections::HashMap::new(),
            setup_map: std::collections::HashMap::new(),
        }
    }

    pub fn get_value(&self, poly: &PolynomialInConstraint, n: usize) -> Result<E::Fr, SynthesisError> {
        match poly {
            PolynomialInConstraint(PolyIdentifier::VariablesPolynomial(_), TimeDilation(_)) => {
                unreachable!("should not try to get value of the state polynomial, get variable first instead");
            },
            PolynomialInConstraint(PolyIdentifier::GateSetupPolynomial(gate_descr, idx), TimeDilation(dilation)) => {
                let final_index = n + dilation;
                let identifier = PolyIdentifier::GateSetupPolynomial(gate_descr, *idx);
                let value = *self.setup_map
                    .get(&identifier)
                    .ok_or(SynthesisError::AssignmentMissing)?
                    .get(final_index)
                    .ok_or(SynthesisError::AssignmentMissing)?;

                Ok(value)
            },
            PolynomialInConstraint(PolyIdentifier::WitnessPolynomial(_), TimeDilation(_)) => {
                unimplemented!()
            },
            _ => {
                unreachable!();
            }
        }
    }

    pub fn get_variable(&self, poly: &PolynomialInConstraint, n: usize) -> Result<Variable, SynthesisError> {
        match poly {
            PolynomialInConstraint(PolyIdentifier::VariablesPolynomial(idx), TimeDilation(dilation)) => {
                let final_index = n + dilation;
                let identifier = PolyIdentifier::VariablesPolynomial(*idx);
                let value = *self.state_map
                    .get(&identifier)
                    .ok_or(SynthesisError::AssignmentMissing)?
                    .get(final_index)
                    .ok_or(SynthesisError::AssignmentMissing)?;

                Ok(value)
            },
            _ => {
                unreachable!("should not try to get variable of setup or witness polynomial");
            }
        }
    }
}

#[derive(Clone)]
pub struct GateDensityStorage<E: Engine>(pub std::collections::HashMap<Box<dyn GateInternal<E>>, BitVec>);

impl<E: Engine> GateDensityStorage<E> {
    pub fn new() -> Self {
        Self(std::collections::HashMap::new())
    }
}

pub struct GateConstantCoefficientsStorage<E: Engine>(pub std::collections::HashMap<Box<dyn GateInternal<E>>, Vec<E::Fr>>);

impl<E: Engine> GateConstantCoefficientsStorage<E> {
    pub fn new() -> Self {
        Self(std::collections::HashMap::new())
    }
}

pub type TrivialAssembly<E, P, MG> = Assembly<E, P, MG, SynthesisModeTesting>;
pub type ProvingAssembly<E, P, MG> = Assembly<E, P, MG, SynthesisModeProve>;
pub type SetupAssembly<E, P, MG> = Assembly<E, P, MG, SynthesisModeGenerateSetup>;

#[derive(Clone)]
pub struct Assembly<E: Engine, P: PlonkConstraintSystemParams<E>, MG: MainGate<E>, S: SynthesisMode> {
    pub inputs_storage: PolynomialStorage<E>,
    pub aux_storage: PolynomialStorage<E>,
    pub num_input_gates: usize,
    pub num_aux_gates: usize,
    pub max_constraint_degree: usize,
    pub main_gate: MG,
    pub input_assingments: Vec<E::Fr>,
    pub aux_assingments: Vec<E::Fr>,
    pub num_inputs: usize,
    pub num_aux: usize,
    pub trace_step_for_batch: Option<usize>,
    pub is_finalized: bool,

    pub gates: std::collections::HashSet<Box<dyn GateInternal<E>>>,
    pub all_queried_polys_in_constraints: std::collections::HashSet<PolynomialInConstraint>,
    // pub sorted_setup_polynomial_ids: Vec<PolyIdentifier>,
    pub sorted_gates: Vec<Box<dyn GateInternal<E>>>,
    pub aux_gate_density: GateDensityStorage<E>,
    pub explicit_zero_variable: Option<Variable>,
    pub explicit_one_variable: Option<Variable>,

    pub tables: Vec<Arc<LookupTableApplication<E>>>,
    pub multitables: Vec<Arc<MultiTableApplication<E>>>,
    pub table_selectors: std::collections::HashMap<String, BitVec>,
    pub multitable_selectors: std::collections::HashMap<String, BitVec>,
    pub table_ids_poly: Vec<E::Fr>,
    pub total_length_of_all_tables: usize,

    pub individual_table_entries: std::collections::HashMap<String, Vec<Vec<E::Fr>>>,
    pub individual_multitable_entries: std::collections::HashMap<String, Vec<Vec<E::Fr>>>,
    pub known_table_ids: Vec<E::Fr>,
    pub num_table_lookups: usize,
    pub num_multitable_lookups: usize,

    _marker_p: std::marker::PhantomData<P>,
    _marker_s: std::marker::PhantomData<S>,
}

impl<E: Engine, P: PlonkConstraintSystemParams<E>, MG: MainGate<E>, S: SynthesisMode> ConstraintSystem<E> for Assembly<E, P, MG, S> {
    type Params = P;
    type MainGate = MG;

    // allocate a variable
    fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {

        self.num_aux += 1;
        let index = self.num_aux;
        if S::PRODUCE_WITNESS {
            let value = value()?;
            self.aux_assingments.push(value);
        }

        Ok(Variable(Index::Aux(index)))
    }

    // allocate an input variable
    fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {
        self.num_inputs += 1;
        let index = self.num_inputs;
        if S::PRODUCE_WITNESS {
            let value = value()?;
            self.input_assingments.push(value);
        }
        
        let input_var = Variable(Index::Input(index));

        let mut main_gate = MainGateTerm::<E>::new();
        main_gate.sub_assign(ArithmeticTerm::from_variable(input_var));

        let dummy = Self::get_dummy_variable();
        let (variables_assignments, coefficients_assignments) = MG::format_term(main_gate, dummy).expect("must make empty padding gate");

        let n = self.num_input_gates;
        Self::allocate_into_storage(
            &MG::default(), 
            &mut self.inputs_storage, 
            n, 
            &coefficients_assignments, 
            &variables_assignments, 
            &[]
        )?;

        self.num_input_gates += 1;

        Ok(input_var)
    }

    fn get_main_gate(&self) -> &MG {
        &self.main_gate
    }

    fn begin_gates_batch_for_step(&mut self) -> Result<(), SynthesisError> {
        debug_assert!(self.trace_step_for_batch.is_none());
        self.num_aux_gates += 1;
        let n = self.num_aux_gates;
        self.trace_step_for_batch = Some(n);

        Ok(())
    }

    fn new_gate_in_batch<G: Gate<E>>(&mut self, 
        gate: &G,
        coefficients_assignments: &[E::Fr],
        variables_assignments: &[Variable],
        witness_assignments: &[E::Fr]
    ) -> Result<(), SynthesisError> {
        // check that gate is ok for config
        // debug_assert!(check_gate_is_allowed_for_params::<E, P, G>(&gate), format!("supplied params do not work with gate {:?}", gate));

        let n = self.trace_step_for_batch.unwrap();
        // make zero-enumerated index
        let n = n - 1;
        
        Self::allocate_into_storage(
            gate,
            &mut self.aux_storage,
            n,
            coefficients_assignments,
            variables_assignments,
            witness_assignments,
        )?;

        self.add_gate_into_list(gate);

        if S::PRODUCE_SETUP {
            if let Some(tracker) = self.aux_gate_density.0.get_mut(gate.as_internal() as &dyn GateInternal<E>) {
                if tracker.len() != n {
                    let padding = n - tracker.len();
                    tracker.grow(padding, false);
                }
                tracker.push(true);
                debug_assert_eq!(n+1, tracker.len());
            } else {
                self.aux_gate_density.0.insert(gate.clone().into_internal(), BitVec::new());
                let tracker = self.aux_gate_density.0.get_mut(gate.as_internal() as &dyn GateInternal<E>).unwrap();
                tracker.grow(n, false);
                tracker.push(true);
                debug_assert_eq!(n+1, tracker.len());
            }
        }

        Ok(())
    }

    fn allocate_variables_without_gate(&mut self, 
        variables_assignments: &[Variable],
        witness_assignments: &[E::Fr]
    ) -> Result<(), SynthesisError> {
        let n = self.trace_step_for_batch.expect("may only be called in a batch");
        // make zero-enumerated index
        let n = n - 1;

        let empty_coefficients = Self::MainGate::empty_coefficients();

        let gate = Self::MainGate::default();

        Self::allocate_into_storage(
            &gate,
            &mut self.aux_storage,
            n,
            &empty_coefficients,
            variables_assignments,
            witness_assignments,
        )?;

        if S::PRODUCE_SETUP {
            let apply_gate = false;

            let tracker = self.aux_gate_density.0.get_mut(gate.as_internal() as &dyn GateInternal<E>).unwrap();
            if tracker.len() != n {
                let padding = n - tracker.len();
                tracker.grow(padding, false);
            }
            tracker.push(apply_gate);
            debug_assert_eq!(n+1, tracker.len());
        }

        Ok(())
    }

    fn end_gates_batch_for_step(&mut self) -> Result<(), SynthesisError> {
        debug_assert!(self.trace_step_for_batch.is_some());
        let n = self.trace_step_for_batch.take().unwrap();
        debug_assert_eq!(n, self.num_aux_gates, "invalid batch id");

        Ok(())
    }

    fn get_value(&self, var: Variable) -> Result<E::Fr, SynthesisError> {
        if !S::PRODUCE_WITNESS {
            return Err(SynthesisError::AssignmentMissing);
        }
        let value = match var {
            Variable(Index::Aux(0)) => {
                // use crate::rand::Rng;

                // let mut rng = crate::rand::thread_rng();
                // let value: E::Fr = rng.gen();

                // value
                E::Fr::zero()
                // return Err(SynthesisError::AssignmentMissing);
            }
            Variable(Index::Input(0)) => {
                return Err(SynthesisError::AssignmentMissing);
            }
            Variable(Index::Input(input)) => {
                self.input_assingments[input - 1]
            },
            Variable(Index::Aux(aux)) => {
                self.aux_assingments[aux - 1]
            }
        };

        Ok(value)
    }

    fn get_dummy_variable() -> Variable {
        Self::dummy_variable()
    }

    fn get_explicit_zero(&mut self) -> Result<Variable, SynthesisError> {
        if let Some(var) = self.explicit_zero_variable {
            return Ok(var);
        }

        let value = E::Fr::zero();
        let zero = self.alloc(|| Ok(value))?;

        let self_term = ArithmeticTerm::from_variable(zero);
        let other_term = ArithmeticTerm::constant(value);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.sub_assign(other_term);

        self.allocate_main_gate(term)?;

        self.explicit_zero_variable = Some(zero);

        Ok(zero)
    }

    fn get_explicit_one(&mut self) -> Result<Variable, SynthesisError> {
        if let Some(var) = self.explicit_one_variable {
            return Ok(var);
        }

        let value = E::Fr::one();
        let one = self.alloc(|| Ok(value))?;

        let self_term = ArithmeticTerm::from_variable(one);
        let other_term = ArithmeticTerm::constant(value);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.sub_assign(other_term);

        self.allocate_main_gate(term)?;

        self.explicit_one_variable = Some(one);

        Ok(one)
    }

    fn add_table(&mut self, table: LookupTableApplication<E>) -> Result<Arc<LookupTableApplication<E>>, SynthesisError> {
        assert!(table.applies_over().len() == 3, "only support tables of width 3");
        assert!(table.can_be_combined(), "can only add tables that are combinable");
        assert!(!self.known_table_ids.contains(&table.table_id()), "can not add a duplicate table for name {}", table.functional_name());
        let table_name = table.functional_name();
        let table_id = table.table_id();
        let number_of_entries = table.size();

        let shared = Arc::from(table);
        let res = shared.clone();

        self.tables.push(shared);
        self.individual_table_entries.insert(table_name.clone(), vec![]);
        self.table_selectors.insert(table_name, BitVec::new());
        self.known_table_ids.push(table_id);

        self.total_length_of_all_tables += number_of_entries;

        Ok(res)
    }

    fn get_table(&self, name: &str) -> Result<Arc<LookupTableApplication<E>>, SynthesisError> {
        for t in self.tables.iter() {
            if t.functional_name() == name {
                return Ok(Arc::clone(t));
            }
        }

        Err(SynthesisError::AssignmentMissing)
    }

    fn add_multitable(&mut self, table: MultiTableApplication<E>) -> Result<(), SynthesisError> {
        let table_name = table.functional_name();
        let mut exists = false;
        for t in self.multitables.iter() {
            if t.functional_name() == table_name {
                exists = true;
            }
        }
        assert!(exists == false);
        self.multitables.push(Arc::from(table));
        self.multitable_selectors.insert(table_name.clone(), BitVec::new());
        self.individual_table_entries.insert(table_name.clone(), vec![]);

        Ok(())
    }

    fn get_multitable(&self, functional_name: &str) -> Result<Arc<MultiTableApplication<E>>, SynthesisError> {
        for t in self.multitables.iter() {
            if t.functional_name() == functional_name {
                return Ok(Arc::clone(t));
            }
        }

        Err(SynthesisError::AssignmentMissing)
    }

    #[track_caller]
    fn apply_single_lookup_gate(&mut self, variables: &[Variable], table: Arc<LookupTableApplication<E>>) -> Result<(), SynthesisError> {
        let n = self.trace_step_for_batch.expect("may only add table constraint in a transaction");
        // make zero-enumerated index
        let n = n - 1;

        if S::PRODUCE_SETUP {
            debug_assert!(self.tables.contains(&table));
            assert!(table.can_be_combined() == true);
            assert!(table.applies_over().len() == 3);

            let table_name = table.functional_name();

            // we need to:
            // - mark that this table applies at this row
            // - add values into the list to later on make a sorted polynomial

            let tracker = self.table_selectors.get_mut(&table_name).unwrap();
            if tracker.len() != n {
                let padding = n - tracker.len();
                tracker.grow(padding, false);
            }
            tracker.push(true);
            debug_assert_eq!(n+1, tracker.len());

            // keep track of what table is applied at what row
            self.table_ids_poly.resize(n, E::Fr::zero());
            self.table_ids_poly.push(table.table_id());
        }

        if S::PRODUCE_WITNESS {
            let table_name = table.functional_name();

            // add values for lookup table sorting later
            let keys_and_values_len = table.applies_over().len();
            let mut table_entries = Vec::with_capacity(keys_and_values_len + 1);
            for v in variables.iter() {
                let value = self.get_value(*v).unwrap();
                table_entries.push(value);
            }
            table_entries.push(table.table_id());        

            let entries = self.individual_table_entries.get_mut(&table_name).unwrap();
            assert_eq!(variables.len(), table.applies_over().len());

            let valid_entries = table.is_valid_entry(&table_entries[..keys_and_values_len]);
            assert!(valid_entries);

            if !valid_entries {
                return Err(SynthesisError::Unsatisfiable);
            }

            entries.push(table_entries);
        }

        self.num_table_lookups += 1;

        Ok(())
    }
    
    #[track_caller]
    fn apply_multi_lookup_gate(&mut self, variables: &[Variable], table: Arc<MultiTableApplication<E>>) -> Result<(), SynthesisError> {
        let n = self.trace_step_for_batch.expect("may only add table constraint in a transaction");
        // make zero-enumerated index
        let n = n - 1;

        if S::PRODUCE_SETUP {
            let table_name = table.functional_name();
            let tracker = self.multitable_selectors.get_mut(&table_name).unwrap();
            if tracker.len() != n {
                let padding = n - tracker.len();
                tracker.grow(padding, false);
            }
            tracker.push(true);
            debug_assert_eq!(n+1, tracker.len());

            self.table_ids_poly.resize(n, E::Fr::zero());
            self.table_ids_poly.push(table.table_id());
        }

        if S::PRODUCE_WITNESS {
            let table_name = table.functional_name();
            let mut table_entries = Vec::with_capacity(table.applies_over().len());
            for v in variables.iter() {
                let value = self.get_value(*v).unwrap();
                table_entries.push(value);
            }
    
            let entries = self.individual_table_entries.get_mut(&table_name).unwrap();
            assert_eq!(variables.len(), table.applies_over().len());
    
            assert!(table.is_valid_entry(&table_entries));

            entries.push(table_entries);
        }

        self.num_multitable_lookups += 1;

        Ok(())
    }

    fn get_current_step_number(&self) -> usize {
        self.n()
    }

    fn get_current_aux_gate_number(&self) -> usize {
        self.num_aux_gates
    }
}

impl<E: Engine, P: PlonkConstraintSystemParams<E>, MG: MainGate<E>, S: SynthesisMode> Assembly<E, P, MG, S> {
    fn allocate_into_storage<G: Gate<E>>(
        gate: &G,
        storage: &mut PolynomialStorage<E>, 
        n: usize,
        coefficients_assignments: &[E::Fr],
        variables_assignments: &[Variable],
        witness_assignments: &[E::Fr]
    ) -> Result<(), SynthesisError> {
        let dummy = Self::get_dummy_variable();
        let zero = E::Fr::zero();

        if S::PRODUCE_SETUP {
            let mut coeffs_it = coefficients_assignments.iter();

            for setup_poly in gate.setup_polynomials().into_iter() {
                let poly_ref = storage.setup_map.entry(setup_poly).or_insert(vec![]);
                if poly_ref.len() < n {
                    poly_ref.resize(n, E::Fr::zero());
                }
                poly_ref.push(*coeffs_it.next().unwrap_or(&zero));
            }

            debug_assert!(coeffs_it.next().is_none(), "must consume all the coefficients for gate");

        }

        let mut variable_it = variables_assignments.iter();

        for var_poly in gate.variable_polynomials().into_iter() {
            let poly_ref = storage.state_map.entry(var_poly).or_insert(vec![]);
            if poly_ref.len() < n {
                poly_ref.resize(n, dummy);
            }
            if poly_ref.len() == n {
                // we consume variable only ONCE
                let var = *variable_it.next().unwrap_or(&dummy);
                poly_ref.push(var);
            }
        }

        debug_assert!(variable_it.next().is_none(), "must consume all variables for gate");

        let mut witness_it = witness_assignments.iter();

        for key in gate.witness_polynomials().into_iter() {
            let poly_ref = storage.witness_map.entry(key).or_insert(vec![]);
            if poly_ref.len() < n {
                poly_ref.resize(n, E::Fr::zero());
            } 
            poly_ref.push(*witness_it.next().unwrap_or(&zero));
        }

        Ok(())
    }

    pub fn n(&self) -> usize {
        self.num_input_gates + self.num_aux_gates
    }

    fn add_gate_into_list<G: Gate<E>>(&mut self, gate: &G) {
        if !self.gates.contains(gate.as_internal() as &dyn GateInternal<E>) {
            self.gates.insert(gate.clone().into_internal());

            // self.add_gate_setup_polys_into_list(gate);
            for p in gate.all_queried_polynomials().into_iter() {
                self.all_queried_polys_in_constraints.insert(p);
            }
            
            self.sorted_gates.push(gate.clone().into_internal());

            let degree = gate.degree();
            if self.max_constraint_degree < degree {
                self.max_constraint_degree = degree;
            }
        }        
    }

    pub fn new() -> Self {
        let mut tmp = Self {
            inputs_storage: PolynomialStorage::new(),
            aux_storage: PolynomialStorage::new(),

            max_constraint_degree: 0,

            num_input_gates: 0,
            num_aux_gates: 0,

            num_inputs: 0,
            num_aux: 0,

            input_assingments: vec![],
            aux_assingments: vec![],

            main_gate: MG::default(),

            trace_step_for_batch: None,

            gates: std::collections::HashSet::new(),
            all_queried_polys_in_constraints: std::collections::HashSet::new(),

            aux_gate_density: GateDensityStorage::new(),

            // sorted_setup_polynomial_ids: vec![],
            sorted_gates: vec![],

            is_finalized: false,

            explicit_zero_variable: None,
            explicit_one_variable: None,

            tables: vec![],
            multitables: vec![],
            table_selectors: std::collections::HashMap::new(),
            multitable_selectors: std::collections::HashMap::new(),
            table_ids_poly: vec![],
            total_length_of_all_tables: 0,

            individual_table_entries: std::collections::HashMap::new(),
            individual_multitable_entries: std::collections::HashMap::new(),

            known_table_ids: vec![],

            num_table_lookups: 0,
            num_multitable_lookups: 0,

            _marker_p: std::marker::PhantomData,
            _marker_s: std::marker::PhantomData,
        };

        tmp.add_gate_into_list(&MG::default());

        tmp
    }

    // return variable that is not in a constraint formally, but has some value
    fn dummy_variable() -> Variable {
        Variable(Index::Aux(0))
    }

    pub fn finalize(&mut self) {
        if self.is_finalized {
            return;
        }

        let mut min_space_for_lookups = self.num_table_lookups;
        for table in self.tables.iter() {
            let table_num_rows = table.size();
            min_space_for_lookups += table_num_rows;
        }
        min_space_for_lookups += self.n();

        let new_size_candidates = [(self.n() + 1).next_power_of_two() - 1, (min_space_for_lookups + 1).next_power_of_two() - 1];

        let new_size = *new_size_candidates.iter().max().unwrap();

        let dummy = Self::get_dummy_variable();

        // let empty_gate = MainGateTerm::<E>::new();
        let empty_vars = vec![dummy; <Self as ConstraintSystem<E>>::Params::STATE_WIDTH];
        let empty_witness = vec![E::Fr::zero(); <Self as ConstraintSystem<E>>::Params::WITNESS_WIDTH];

        // let mg = MG::default();

        for _ in self.n()..new_size {

            self.begin_gates_batch_for_step().unwrap();

            self.allocate_variables_without_gate(
                &empty_vars,
                &empty_witness
            ).unwrap();

            self.end_gates_batch_for_step().unwrap();

            // self.new_single_gate_for_trace_step(
            //     &mg, 
            //     &coeffs, 
            //     &vars,
            //     &[]
            // ).expect("must add padding gate");
        }

        let new_size_for_aux = new_size - self.num_input_gates;

        if S::PRODUCE_SETUP {
            // pad gate selectors
            for (_, tracker) in self.aux_gate_density.0.iter_mut() {
                tracker.grow(new_size_for_aux, false);
            }

            // pad lookup selectors
            for (_, selector) in self.table_selectors.iter_mut() {
                selector.grow(new_size_for_aux, false);
            }

            // pad special purpose table selector poly
            self.table_ids_poly.resize(new_size_for_aux, E::Fr::zero());
        }

        assert!((self.n()+1).is_power_of_two());
        self.is_finalized = true;
    }

    fn get_storage_for_trace_step(&self, step: usize) -> &PolynomialStorage<E> {
        if step < self.num_input_gates {
            &self.inputs_storage
        } else {
            &self.aux_storage
        }
    }

    pub fn is_satisfied(&self) -> bool {
        if !S::PRODUCE_SETUP || !S::PRODUCE_WITNESS {
            // only testing mode can run this check for now
            return true;
        }
        // expect a small number of inputs

        if self.n() == 0 {
            return true;
        }

        // TODO: handle public inputs

        // for i in 0..self.num_input_gates {
        //     let gate = self.input_assingments
        // }

        // let one = E::Fr::one();
        // let mut minus_one = E::Fr::one();
        // minus_one.negate();

        let n = self.n() - 1;

        let worker = Worker::new();

        let storage = self.make_assembled_poly_storage(&worker, false).unwrap();

        for (gate_type, density) in self.aux_gate_density.0.iter() {
            for (gate_index, is_applicable) in density.iter().enumerate() {
                if is_applicable == false {
                    continue;
                }

                let trace_index = self.num_input_gates + gate_index;

                let last = trace_index == n;

                let value = gate_type.verify_on_row(trace_index, &storage, last);

                if value.is_zero() == false {
                    println!("Unsatisfied at aux gate {} (zero enumerated)", gate_index);
                    println!("Constraint value = {}", value);
                    println!("Gate {:?}", gate_type.name());
                    return false;
                }
            }
        }

        true
    }

    pub(crate) async fn make_permutations(&self, old_worker: &Worker, worker: NewWorker, is_background: bool) -> Result<Vec<Polynomial::<E::Fr, Values>>, SynthesisError> {
        assert!(self.is_finalized);

        if !S::PRODUCE_SETUP {
            return Err(SynthesisError::AssignmentMissing);
        }

        let num_gates = self.n();
        let num_partitions = self.num_inputs + self.num_aux;
        let num_inputs = self.num_inputs;
        // in the partition number i there is a set of indexes in V = (a, b, c) such that V_j = i
        let mut partitions = vec![vec![]; num_partitions + 1];

        let mut poly_ids = vec![];
        for i in 0..P::STATE_WIDTH {
            let id = PolyIdentifier::VariablesPolynomial(i);
            poly_ids.push(id);
        }

        // gate_idx is zero-enumerated here
        for gate_idx in 0..num_gates
        {
            let storage = self.get_storage_for_trace_step(gate_idx);
            for (state_poly_index, poly_id) in poly_ids.iter().enumerate() {
                let variables_vec_ref = storage.state_map.get(&poly_id).expect("must get a variables polynomial");
                let storage_idx = if gate_idx < self.num_input_gates {
                    gate_idx
                } else {
                    gate_idx - self.num_input_gates
                };

                let v = variables_vec_ref[storage_idx];
                match v {
                    Variable(Index::Aux(0)) => {
                        // Dummy variables do not participate in the permutation
                    },
                    Variable(Index::Input(0)) => {
                        unreachable!("There must be no input with index 0");
                    },
                    Variable(Index::Input(index)) => {
                        let i = index; // inputs are [1, num_inputs]
                        partitions[i].push((state_poly_index, gate_idx+1));
                    },
                    Variable(Index::Aux(index)) => {
                        let i = index + num_inputs; // aux are [num_inputs + 1, ..]
                        partitions[i].push((state_poly_index, gate_idx+1));
                    },
                }
            }
        }

        // sanity check
        assert_eq!(partitions[0].len(), 0);

        let domain = Domain::new_for_size(num_gates as u64).expect("must have enough roots of unity to fit the circuit");

        // now we need to make root at it's cosets
        let domain_elements = materialize_domain_elements_with_natural_enumeration(
            &domain, &old_worker
        );

        // domain_elements.pop().unwrap();

        use crate::ff::SqrtField;
        use crate::ff::LegendreSymbol;

        let mut non_residues = vec![];
        non_residues.push(E::Fr::one());
        non_residues.extend(make_non_residues::<E::Fr>(P::STATE_WIDTH - 1));

        assert_eq!(non_residues.len(), 4);

        let mut sigmas = vec![];
        for i in 0..P::STATE_WIDTH {
            let mut sigma_i = Polynomial::from_values_unpadded(domain_elements.clone()).unwrap();
            sigma_i.scale(worker.child(), false,  non_residues[i]).await;
            sigmas.push(sigma_i);
        }

        let mut permutations = vec![vec![]; num_partitions + 1];

        fn rotate<T: Sized>(mut vec: Vec<T>) -> Vec<T> {
            if vec.len() > 1 {
                let mut els: Vec<_> = vec.drain(0..1).collect();
                debug_assert_eq!(els.len(), 1);
                // els.reverse();
                vec.push(els.pop().unwrap());
            }

            vec
        }

        for (i, partition) in partitions.into_iter().enumerate().skip(1) {
            // copy-permutation should have a cycle around the partition

            // we do not need to permute over partitions of length 1,
            // as this variable only happends in one place
            if partition.len() == 1 {
                continue;
            }

            let permutation = rotate(partition.clone());
            permutations[i] = permutation.clone();

            for (original, new) in partition.into_iter()
                                    .zip(permutation.into_iter()) 
            {
                // (column_idx, trace_step_idx)
                let new_zero_enumerated = new.1 - 1;
                let mut new_value = domain_elements[new_zero_enumerated];

                // we have shuffled the values, so we need to determine FROM
                // which of k_i * {1, omega, ...} cosets we take a value
                // for a permutation polynomial
                new_value.mul_assign(&non_residues[new.0]);

                // check to what witness polynomial the variable belongs
                let place_into = &mut sigmas[original.0].as_mut();

                let original_zero_enumerated = original.1 - 1;
                place_into[original_zero_enumerated] = new_value;
            }
        }

        Ok(sigmas)
    }

    fn make_setup_polynomials(
        &self,
        with_finalization: bool
    ) -> Result<std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Values>>, SynthesisError> {
        if with_finalization {
            assert!(self.is_finalized);
        }

        if !S::PRODUCE_SETUP {
            return Err(SynthesisError::AssignmentMissing);
        }

        let total_num_gates = self.n();
        let num_input_gates = self.num_input_gates;

        let mut map = std::collections::HashMap::new();

        let setup_poly_ids: Vec<_> = self.aux_storage.setup_map.keys().collect();

        for &id in setup_poly_ids.into_iter() {
            let mut assembled_poly = vec![E::Fr::zero(); total_num_gates];
            if num_input_gates != 0 {
                let input_gates_coeffs = &mut assembled_poly[..num_input_gates];
                input_gates_coeffs.copy_from_slice(&self.inputs_storage.setup_map.get(&id).unwrap()[..]);
            }

            {
                let src = &self.aux_storage.setup_map.get(&id).unwrap()[..];
                let src_len = src.len();
                let aux_gates_coeffs = &mut assembled_poly[num_input_gates..(num_input_gates+src_len)];
                aux_gates_coeffs.copy_from_slice(src);
            }

            let as_poly = Polynomial::from_values_unpadded(assembled_poly)?;

            map.insert(id, as_poly);
        }

        Ok(map)
    }

    #[track_caller]
    pub async fn create_setup<C: Circuit<E>>(
        &self,
        old_worker: &Worker,
        worker: NewWorker, 
        is_background: bool,
    ) -> Result<Setup<E, C>, SynthesisError> {
        assert!(self.is_finalized);

        assert!(S::PRODUCE_SETUP);

        let claimed_gates_list = C::declare_used_gates()?;
        let known_gates_list = &self.sorted_gates;

        assert_eq!(&claimed_gates_list, known_gates_list, "trying to perform setup for a circuit that has different gates set from synthesized one: circuit claims {:?}, in synthesis we had {:?}", &claimed_gates_list, &known_gates_list);

        // check for consistency
        {
            assert!(&<Self as ConstraintSystem<E>>::MainGate::default().into_internal() == &claimed_gates_list[0]);
            assert!(&C::MainGate::default().into_internal() == &claimed_gates_list[0]);
            // dbg!(&claimed_gates_list[0]);
            // let as_any = (&claimed_gates_list[0]) as &dyn std::any::Any;
            // match as_any.downcast_ref::<<Self as ConstraintSystem<E>>::MainGate>() {
            //     Some(..) => {

            //     },
            //     None => {
            //         println!("Type mismatch: first gate among used gates must be the main gate of CS");
            //         // panic!("first gate among used gates must be the main gate of CS");
            //     }
            // }
        }

        let mut setup = Setup::<E, C>::empty();

        setup.n = self.n();
        setup.num_inputs = self.num_inputs;
        setup.state_width = <Self as ConstraintSystem<E>>::Params::STATE_WIDTH;
        setup.num_witness_polys = <Self as ConstraintSystem<E>>::Params::WITNESS_WIDTH;

        setup.non_residues = make_non_residues::<E::Fr>(setup.state_width - 1);

        let (mut setup_polys_values_map, permutation_polys) = self.perform_setup(&old_worker, worker.child(), is_background).await?;
        for gate in known_gates_list.iter() {
            let setup_polys = gate.setup_polynomials();
            for id in setup_polys.into_iter() {
                let values = setup_polys_values_map.remove(&id).expect("must contain setup poly").clone_padded_to_domain()?;
                let mon = values.icoset_fft_for_generator(&old_worker, worker.child(), false, &E::Fr::one()).await;

                setup.gate_setup_monomials.push(mon);
            }
        }

        for perm in permutation_polys.into_iter() {
            let mon = perm.icoset_fft_for_generator(&old_worker,worker.child(), false, &E::Fr::one()).await;

            setup.permutation_monomials.push(mon);
        }

        let gate_selector_values = self.output_gate_selectors(&old_worker)?;
        
        if known_gates_list.len() > 1 {
            assert_eq!(gate_selector_values.len(), known_gates_list.len(), "numbers of selectors and known gates mismatch");
        }

        for values in gate_selector_values.into_iter() {
            let poly = Polynomial::from_values(values)?;
            let mon = poly.icoset_fft_for_generator(&old_worker,worker.child(), false, &E::Fr::one()).await;

            setup.gate_selectors_monomials.push(mon);
        }

        if self.tables.len() > 0 && self.num_table_lookups > 0 {
            // we have lookup tables, so add them to setup

            let num_lookups = self.num_table_lookups;
            setup.total_lookup_entries_length = num_lookups;

            let table_tails = self.calculate_t_polynomial_values_for_single_application_tables()?;
            assert_eq!(table_tails.len(), 4);

            let tails_len = table_tails[0].len();

            // total number of gates, Input + Aux
            let size = self.n();

            let copy_start = size - tails_len;

            for tail in table_tails.into_iter() {
                let mut values = vec![E::Fr::zero(); size];
                values[copy_start..].copy_from_slice(&tail[..]);

                let poly = Polynomial::from_values(values)?;
                let mon = poly.icoset_fft_for_generator(&old_worker,worker.child(), false, &E::Fr::one()).await;

                setup.lookup_tables_monomials.push(mon);
            }

            let selector_for_lookup_values = self.calculate_lookup_selector_values()?;
            let poly = Polynomial::from_values(selector_for_lookup_values)?;
            let mon = poly.icoset_fft_for_generator(&old_worker,worker.child(), false, &E::Fr::one()).await;
            setup.lookup_selector_monomial = Some(mon);

            let table_type_values = self.calculate_table_type_values()?;
            let poly = Polynomial::from_values(table_type_values)?;
            let mon = poly.icoset_fft_for_generator(&old_worker,worker.child(), false, &E::Fr::one()).await;
            setup.lookup_table_type_monomial = Some(mon);
        }

        Ok(setup)
    }

    pub async fn perform_setup(
        &self, 
        old_worker: &Worker,
        worker: NewWorker,
        is_background: bool, 
    ) -> Result<
    (std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Values>>, Vec<Polynomial<E::Fr, Values>>), 
    SynthesisError
    > {
        let map = self.make_setup_polynomials(true)?;
        let permutation_polys = self.make_permutations(&old_worker, worker, is_background).await?;

        Ok((map, permutation_polys))
    }

    pub fn output_gate_selectors(&self, worker: &Worker) -> Result<Vec<Vec<E::Fr>>, SynthesisError> {
        if self.sorted_gates.len() == 1 {
            return Ok(vec![]);
        }

        let num_gate_selectors = self.sorted_gates.len();

        let one = E::Fr::one();
        let empty_poly_values = vec![E::Fr::zero(); self.n()];
        let mut poly_values = vec![empty_poly_values.clone(); num_gate_selectors];
        let num_input_gates = self.num_input_gates;

        // first gate in sorted in a main gate and applies on public inputs
        for p in poly_values[0][..num_input_gates].iter_mut() {
            *p = one;
        }

        worker.scope(poly_values.len(), |scope, chunk| {
            for (i, lh) in poly_values.chunks_mut(chunk)
                            .enumerate() {
                scope.spawn(move |_| {
                    // we take `values_per_leaf` values from each of the polynomial
                    // and push them into the conbinations
                    let base_idx = i*chunk;
                    for (j, lh) in lh.iter_mut().enumerate() {
                        let idx = base_idx + j;
                        let id = &self.sorted_gates[idx];
                        let density = self.aux_gate_density.0.get(id).unwrap();
                        let poly_mut_slice: &mut [E::Fr] = &mut lh[num_input_gates..];
                        for (i, d) in density.iter().enumerate() {
                            if d {
                                poly_mut_slice[i] = one;
                            }
                        }
                    }
                });
            }
        });

        Ok(poly_values)
    }

    pub fn calculate_t_polynomial_values_for_single_application_tables(&self) -> 
        Result<Vec<Vec<E::Fr>>, SynthesisError> {

        if !S::PRODUCE_SETUP {
            return Err(SynthesisError::AssignmentMissing);
        }
        
        if self.tables.len() == 0 {
            return Ok(vec![])
        }
        
        // we should pass over every table and append it

        let mut width = 0;
        for table in self.tables.iter() {
            if width == 0 {
                width = table.width();
            } else {
                assert_eq!(width, table.width());
            }
        }

        assert_eq!(width, 3, "only support tables that span over 3 polynomials for now");

        let mut column_contributions = vec![vec![]; width + 1];

        for table in self.tables.iter() {
            let entries = table.get_table_values_for_polys();
            // these are individual column vectors, so just copy
            for (idx, e) in entries.into_iter().enumerate() {
                column_contributions[idx].extend(e);
            }

            let table_id = table.table_id();
            let pad_to_len = column_contributions[0].len();

            column_contributions.last_mut().unwrap().resize(pad_to_len, table_id);
        }


        Ok(column_contributions)
    }

    pub fn calculate_interleaved_t_polys(&self) -> 
        Result<Vec<Vec<E::Fr>>, SynthesisError> {
        assert!(self.is_finalized);
        
        if self.tables.len() == 0 {
            return Ok(vec![])
        }
        
        // we should pass over every table and append it

        let mut width = 0;
        for table in self.tables.iter() {
            if width == 0 {
                width = table.width();
            } else {
                assert_eq!(width, table.width());
            }
        }

        assert_eq!(width, 3, "only support tables that span over 3 polynomials for now");

        assert!(self.is_finalized);
        if self.tables.len() == 0 {
            return Ok(vec![]);
        }

        // total number of gates, Input + Aux
        let size = self.n();

        let aux_gates_start = self.num_input_gates;

        let mut contributions = vec![vec![E::Fr::zero(); size]; 4];

        // make it shifted for ease of rotations later one
        let mut place_into_idx = aux_gates_start + 1;

        let lookup_selector = self.calculate_lookup_selector_values()?;

        for single_application in self.tables.iter() {
            let entries = single_application.get_table_values_for_polys();
            assert_eq!(entries.len(), 3);
            let table_id = single_application.table_id();
            let num_entries = single_application.size();

            assert_eq!(entries[0].len(), num_entries);

            for entry_idx in 0..num_entries {
                'inner: loop {
                    if lookup_selector[place_into_idx].is_zero() {
                        // we can place a table row into the poly
                        for column in 0..3 {
                            contributions[column][place_into_idx] = entries[column][entry_idx];
                        }
                        contributions[3][place_into_idx] = table_id;
                        place_into_idx += 1;

                        break 'inner;
                    } else {
                        // go for a next one 
                        place_into_idx += 1;
                    }
                }
            }
        }

        Ok(contributions)
    }

    pub fn calculate_s_poly_contributions_from_witness(&self) ->
        Result<Vec<Vec<E::Fr>>, SynthesisError> 
    {
        if self.tables.len() == 0 {
            return Ok(vec![]);
        }
        // we first form a set of all occured witness values,
        // then include table entries to the set
        // and then sort this set

        let mut kv_set_entries = vec![];
        let mut contributions_per_column = vec![vec![]; 4];
        for single_application in self.tables.iter() {
            // copy all queries from witness
            let table_name = single_application.functional_name();
            for kv_values in self.individual_table_entries.get(&table_name).unwrap() {
                let entry = KeyValueSet::<E>::from_slice(&kv_values[..3]);
                kv_set_entries.push(entry);
            }

            // copy table elements themselves

            let entries = single_application.get_table_values_for_polys();
            // those are full values of polynomials, so we have to virtually transpose

            let size = entries[0].len();
            for i in 0..size {
                let entry = KeyValueSet::new([entries[0][i], entries[1][i], entries[2][i]]);
                kv_set_entries.push(entry)
            }

            kv_set_entries.sort();

            // now copy backward with addition of the table id

            for kv in kv_set_entries.iter() {
                for i in 0..3 {
                    contributions_per_column[i].push(kv.inner[i]);
                }
            }

            let table_id = single_application.table_id();
            let pad_to_len = contributions_per_column[0].len();
            contributions_per_column.last_mut().unwrap().resize(pad_to_len, table_id);

            kv_set_entries.truncate(0);
        }

        Ok(contributions_per_column)
    }

    pub fn calculate_table_type_values(
        &self
    ) -> 
        Result<Vec<E::Fr>, SynthesisError>
    {
        assert!(self.is_finalized);

        if !S::PRODUCE_SETUP {
            return Err(SynthesisError::AssignmentMissing);
        }

        if self.tables.len() == 0 {
            return Ok(vec![]);
        }

        let table_ids_vector_on_aux_gates = &self.table_ids_poly;

        let num_aux_gates = self.num_aux_gates;

        // total number of gates, Input + Aux
        let size = self.n();

        let aux_gates_start = self.num_input_gates;
        let aux_gates_end = aux_gates_start + num_aux_gates;

        let mut values = vec![E::Fr::zero(); size];
        assert_eq!(num_aux_gates, table_ids_vector_on_aux_gates.len());

        values[aux_gates_start..aux_gates_end].copy_from_slice(table_ids_vector_on_aux_gates);

        Ok(values)
    }

    pub fn calculate_lookup_selector_values(
        &self
    ) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(self.is_finalized);

        if !S::PRODUCE_SETUP {
            return Err(SynthesisError::AssignmentMissing);
        }

        if self.tables.len() == 0 {
            return Ok(vec![]);
        }

        // total number of gates, Input + Aux
        let size = self.n();

        let aux_gates_start = self.num_input_gates;

        let num_aux_gates = self.num_aux_gates;
        // input + aux gates without t-polys

        let mut lookup_selector_values = vec![E::Fr::zero(); size];

        for single_application in self.tables.iter() {
            let table_name = single_application.functional_name();
            let selector_bitvec = self.table_selectors.get(&table_name).unwrap();

            for aux_gate_idx in 0..num_aux_gates {
                if selector_bitvec[aux_gate_idx] {
                    let global_gate_idx = aux_gate_idx + aux_gates_start;
                    // place 1 into selector
                    lookup_selector_values[global_gate_idx] = E::Fr::one();
                }
            }
        }

        Ok(lookup_selector_values)
    }

    pub fn calculate_masked_lookup_entries(
        &self,
        storage: &AssembledPolynomialStorage<E>
    ) -> 
        Result<Vec<Vec<E::Fr>>, SynthesisError>
    {
        assert!(self.is_finalized);
        if self.tables.len() == 0 {
            return Ok(vec![]);
        }

        // total number of gates, Input + Aux
        let size = self.n();

        let aux_gates_start = self.num_input_gates;

        let num_aux_gates = self.num_aux_gates;
        // input + aux gates without t-polys

        let mut contributions_per_column = vec![vec![E::Fr::zero(); size]; 3];
        for single_application in self.tables.iter() {
            let table_name = single_application.functional_name();
            let keys_and_values = single_application.applies_over();
            let selector_bitvec = self.table_selectors.get(&table_name).unwrap();

            for aux_gate_idx in 0..num_aux_gates {
                if selector_bitvec[aux_gate_idx] {
                    let global_gate_idx = aux_gate_idx + aux_gates_start;

                    // place value into f poly
                    for (idx, &poly_id) in keys_and_values.iter().enumerate() {
                        let value = storage.get_poly_at_step(poly_id, global_gate_idx);
                        contributions_per_column[idx][global_gate_idx] = value;
                    }
                }
            }
        }

        Ok(contributions_per_column)
    }

    pub fn calculate_masked_lookup_entries_using_selector<'a>(
        &self,
        storage: &AssembledPolynomialStorage<E>,
        selector: &PolynomialProxy<'a, E::Fr, Values>
    ) -> 
        Result<Vec<Vec<E::Fr>>, SynthesisError>
    {
        assert!(self.is_finalized);
        if self.tables.len() == 0 {
            return Ok(vec![]);
        }

        // total number of gates, Input + Aux
        let size = self.n();

        let aux_gates_start = self.num_input_gates;

        let num_aux_gates = self.num_aux_gates;
        // input + aux gates without t-polys

        let selector_ref = selector.as_ref().as_ref();

        let one = E::Fr::one();

        let mut contributions_per_column = vec![vec![E::Fr::zero(); size]; 3];
        for single_application in self.tables.iter() {
            let keys_and_values = single_application.applies_over();

            for aux_gate_idx in 0..num_aux_gates {
                let global_gate_idx = aux_gate_idx + aux_gates_start;

                if selector_ref[global_gate_idx] == one {
                    // place value into f poly
                    for (idx, &poly_id) in keys_and_values.iter().enumerate() {
                        let value = storage.get_poly_at_step(poly_id, global_gate_idx);
                        contributions_per_column[idx][global_gate_idx] = value;
                    }
                }
            }
        }

        Ok(contributions_per_column)
    }

    fn sort_by_t(
        witness_entries: &Vec<Vec<E::Fr>>,
        table_entries: &Vec<Vec<E::Fr>>,
    ) -> Result< Vec<Vec<E::Fr>>, SynthesisError> {
        assert_eq!(witness_entries.len(), table_entries.len());

        if witness_entries.len() == 0 {
            return Ok(vec![]);
        }

        // make s = f sorted by t (elements in s appear in the same order as elements in t)

        let entries_len = table_entries[0].len();
        let witnesses_len = witness_entries[0].len();

        let mut index_lookups_for_sorting = vec![std::collections::HashMap::with_capacity(entries_len); witness_entries.len()];

        for (idx, table) in table_entries.iter().enumerate() {
            for (entry_index, &entry_value) in table.iter().enumerate() {
                // make a reverse lookup field element -> index
                index_lookups_for_sorting[idx].insert(entry_value, entry_index);
            }
        }

        let mut column_contributions = vec![];

        for (idx, witness_column) in witness_entries.iter().enumerate() {
            let mut indexes = vec![usize::max_value(); witnesses_len];
            for (witness_index, witness_value) in witness_column.iter().enumerate() {
                let reverse_lookup_index = index_lookups_for_sorting[idx].get(witness_value).unwrap();
                indexes[witness_index] = *reverse_lookup_index;
            }

            indexes.sort();

            println!("sorted_index = {:?}", indexes);

            let mut s_for_column = Vec::with_capacity(witnesses_len);

            for sorted_index in indexes.into_iter() {
                let table = &table_entries[idx];
                s_for_column.push(table[sorted_index]);
            }

            column_contributions.push(s_for_column);
        }


        Ok(column_contributions)
    }

    pub fn make_state_and_witness_polynomials(
        &self,
        worker: &Worker,
        with_finalization: bool
    ) -> Result<(Vec<Vec<E::Fr>>, Vec<Vec<E::Fr>>), SynthesisError>
    {
        if with_finalization {
            assert!(self.is_finalized);
        }

        if !S::PRODUCE_WITNESS {
            return Err(SynthesisError::AssignmentMissing);
        }

        let mut full_assignments = if with_finalization {
            vec![Vec::with_capacity((self.n()+1).next_power_of_two()); P::STATE_WIDTH]
        } else {
            vec![Vec::with_capacity(self.n()+1); P::STATE_WIDTH]
        };

        let pad_to = if with_finalization {
            (self.n()+1).next_power_of_two()
        } else {
            self.n()+1
        };

        let num_input_gates = self.num_input_gates;
        let num_aux_gates = self.num_aux_gates;

        full_assignments[0].extend_from_slice(&self.input_assingments);
        assert!(full_assignments[0].len() == num_input_gates);
        for i in 1..P::STATE_WIDTH {
            full_assignments[i].resize(num_input_gates, E::Fr::zero());
        }

        let dummy = Self::get_dummy_variable();

        worker.scope(full_assignments.len(), |scope, chunk| {
            for (i, lh) in full_assignments.chunks_mut(chunk)
                            .enumerate() {
                scope.spawn(move |_| {
                    // we take `values_per_leaf` values from each of the polynomial
                    // and push them into the conbinations
                    let base_idx = i*chunk;
                    for (j, lh) in lh.iter_mut().enumerate() {
                        let idx = base_idx + j;
                        let id = PolyIdentifier::VariablesPolynomial(idx);
                        let poly_ref = self.aux_storage.state_map.get(&id).unwrap();
                        for i in 0..num_aux_gates {
                            let var = poly_ref.get(i).unwrap_or(&dummy);
                            let value = self.get_value(*var).unwrap();
                            lh.push(value);
                        }
                    }
                });
            }
        });

        for p in full_assignments.iter_mut() {
            p.resize(pad_to - 1, E::Fr::zero());
        }

        for a in full_assignments.iter() {
            assert_eq!(a.len(), pad_to - 1);
        }

        Ok((full_assignments, vec![]))
    }

    pub fn make_assembled_poly_storage(
        &self, 
        worker: &Worker, 
        with_finalization: bool
    ) -> Result<AssembledPolynomialStorage<E>, SynthesisError> {
        if with_finalization {
            assert!(self.is_finalized);
        }
        
        let (state_polys, witness_polys) = self.make_state_and_witness_polynomials(&worker, with_finalization)?;

        let mut state_polys_map = std::collections::HashMap::new();
        for (idx, poly) in state_polys.into_iter().enumerate() {
            let key = PolyIdentifier::VariablesPolynomial(idx);
            let p = Polynomial::from_values_unpadded(poly)?;
            // let p = PolynomialProxy::from_owned(p);
            state_polys_map.insert(key, p);
        }

        let mut witness_polys_map = std::collections::HashMap::new();
        for (idx, poly) in witness_polys.into_iter().enumerate() {
            let key = PolyIdentifier::WitnessPolynomial(idx);
            let p = Polynomial::from_values_unpadded(poly)?;
            // let p = PolynomialProxy::from_owned(p);
            witness_polys_map.insert(key, p);
        }

        let mut setup_map = std::collections::HashMap::new();
        let mut gate_selectors_map = std::collections::HashMap::new();

        if S::PRODUCE_SETUP {
            let setup_polys_map = self.make_setup_polynomials(with_finalization)?;
            let gate_selectors = self.output_gate_selectors(&worker)?;

            for (gate, poly) in self.sorted_gates.iter().zip(gate_selectors.into_iter()) {
                // let key = gate.clone();
                let key = PolyIdentifier::GateSelector(gate.name());
                let p = Polynomial::from_values_unpadded(poly)?;
                // let p = PolynomialProxy::from_owned(p);
                gate_selectors_map.insert(key, p);
            }

            for (key, p) in setup_polys_map.into_iter() {
                // let p = PolynomialProxy::from_owned(p);
                setup_map.insert(key, p);
            }
        }

        let assembled = AssembledPolynomialStorage::<E> {
            state_map: state_polys_map,
            witness_map: witness_polys_map,
            setup_map: setup_map,
            scratch_space: std::collections::HashMap::new(),
            gate_selectors: gate_selectors_map,
            named_polys: std::collections::HashMap::new(),
            is_bitreversed: false,
            lde_factor: 1
        };

        Ok(assembled)
    }

    pub async fn create_monomial_storage_async(
        old_worker: &Worker,
        worker: NewWorker,
        async_manager: Arc<AsyncWorkManager<E>>,   
        // omegas_inv: &OmegasInvBitreversed<E::Fr>,     
        value_form_storage: &AssembledPolynomialStorage< E>,
        include_setup: bool,
        is_background: bool,
    ) -> Result<AssembledPolynomialStorageForMonomialForms<E>, SynthesisError> {
        assert_eq!(value_form_storage.lde_factor, 1);
        assert!(value_form_storage.is_bitreversed == false);

        let mut monomial_storage = AssembledPolynomialStorageForMonomialForms::<E>::new();

        for (&k, v) in value_form_storage.state_map.iter() {
            // let mon_form = v.as_ref().clone_padded_to_domain()?.ifft_using_bitreversed_ntt(
            //     &worker, 
            //     omegas_inv, 
            //     &E::Fr::one()
            // )?;
            // let mon_form = PolynomialProxy::from_owned(mon_form);
            let coeffs = async_manager.ifft(v.clone_padded_to_domain()?.arc_coeffs(), worker.child(), is_background).await;
            let mut mon_form = Polynomial::from_coeffs(coeffs).unwrap();
            mon_form.bitreverse_enumeration(worker.child(), false).await;
            // let mon_form = PolynomialProxy::from_owned(mon_form);
            monomial_storage.state_map.insert(k, mon_form);
        }

        for (&k, v) in value_form_storage.witness_map.iter() {
            // let mon_form = v.as_ref().clone_padded_to_domain()?.ifft_using_bitreversed_ntt(
            //     &worker, 
            //     omegas_inv, 
            //     &E::Fr::one()
            // )?;
            // let mon_form = PolynomialProxy::from_owned(mon_form);
            let coeffs = async_manager.ifft(v.clone_padded_to_domain()?.arc_coeffs(), worker.child(), is_background).await;
            let mut mon_form = Polynomial::from_coeffs(coeffs).unwrap();
            mon_form.bitreverse_enumeration(worker.child(), false).await;
            // let mon_form = PolynomialProxy::from_owned(mon_form);
            monomial_storage.witness_map.insert(k, mon_form);
        }

        if include_setup {
            for (&k, v) in value_form_storage.gate_selectors.iter() {
                // let mon_form = v.as_ref().clone_padded_to_domain()?.ifft_using_bitreversed_ntt(
                //     &worker, 
                //     omegas_inv, 
                //     &E::Fr::one()
                // )?;
                // let mon_form = PolynomialProxy::from_owned(mon_form);
                let coeffs = async_manager.ifft(v.clone_padded_to_domain()?.arc_coeffs(), worker.child(), is_background).await;
                let mut mon_form = Polynomial::from_coeffs(coeffs).unwrap();
                mon_form.bitreverse_enumeration(worker.child(), false).await;
                // let mon_form = PolynomialProxy::from_owned(mon_form);
                monomial_storage.gate_selectors.insert(k, mon_form);
            }

            for (&k, v) in value_form_storage.setup_map.iter() {
                // let mon_form = v.as_ref().clone_padded_to_domain()?.ifft_using_bitreversed_ntt(
                //     &worker, 
                //     omegas_inv, 
                //     &E::Fr::one()
                // )?;
                // let mon_form = PolynomialProxy::from_owned(mon_form);
                let coeffs = async_manager.ifft(v.clone_padded_to_domain()?.arc_coeffs(), worker.child(), is_background).await;
                let mut mon_form = Polynomial::from_coeffs(coeffs).unwrap();
                mon_form.bitreverse_enumeration(worker.child(), false).await;
                // let mon_form = PolynomialProxy::from_owned(mon_form);
                // let mon_form = PolynomialProxy::from_owned(Polynomial::from_coeffs(mon_form).unwrap());
                monomial_storage.setup_map.insert(k, mon_form);
            }
        }

        Ok(monomial_storage)
    }
}
