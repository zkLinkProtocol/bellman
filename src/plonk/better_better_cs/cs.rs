use crate::pairing::ff::{Field};
use crate::pairing::{Engine};
use crate::bit_vec::BitVec;

use crate::{SynthesisError};
use std::marker::PhantomData;

pub use crate::plonk::cs::variable::*;

pub trait Circuit<E: Engine> {
    fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError>;
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum PolynomialInConstraint {
    VariablesPolynomial(usize, TimeDilation),
    WitnessPolynomial(usize, TimeDilation),
    SetupPolynomial(&'static str, usize, TimeDilation)
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum Coefficient {
    PlusOne,
    MinusOne,
    Other
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum PolyIdentifier {
    VariablesPolynomial(usize),
    WitnessPolynomial(usize),
    SetupPolynomial(&'static str, usize),
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct TimeDilation(pub usize);

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct PolynomialMultiplicativeTerm(pub Coefficient, pub Vec<PolynomialInConstraint>);

impl PolynomialMultiplicativeTerm {
    fn degree(&self) -> usize {
        self.1.len()
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct LinearCombinationOfTerms(pub Vec<PolynomialMultiplicativeTerm>);

impl LinearCombinationOfTerms {
    fn terms(&self) -> &[PolynomialMultiplicativeTerm] {
       &self.0[..]
    }
}

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

pub struct MainGateTerm<E: Engine>{
    terms: Vec<ArithmeticTerm<E>>,
    num_multiplicative_terms: usize,
    num_constant_terms: usize
}

impl<E: Engine> MainGateTerm<E> {
    pub fn new() -> Self {
        Self {
            terms: Vec::with_capacity(8),
            num_multiplicative_terms: 0,
            num_constant_terms: 0
        }
    }

    pub fn add_assign(&mut self, other: ArithmeticTerm<E>) {
        match &other {
            ArithmeticTerm::Product(_, _) => {
                self.num_multiplicative_terms += 1;
                self.terms.push(other);
            },
            ArithmeticTerm::SingleVariable(_, _) => {
                self.terms.push(other);
            },
            ArithmeticTerm::Constant(_) => {
                self.num_constant_terms += 1;
                self.terms.push(other);
            },
        }

        debug_assert!(self.num_constant_terms <= 1, "must not duplicate constants");        
    }

    pub fn sub_assign(&mut self, mut other: ArithmeticTerm<E>) {
        match &mut other {
            ArithmeticTerm::Product(_, ref mut coeff) => {
                coeff.negate();
                self.num_multiplicative_terms += 1;
            },
            ArithmeticTerm::SingleVariable(_, ref mut coeff) => {
                coeff.negate();
            },
            ArithmeticTerm::Constant(ref mut coeff) => {
                coeff.negate();
                self.num_constant_terms += 1;       
            },
        }

        self.terms.push(other);

        debug_assert!(self.num_constant_terms <= 1, "must not duplicate constants");        
    }
}

pub trait MainGateEquation: GateEquation {
    const NUM_LINEAR_TERMS: usize;
    const NUM_VARIABLES: usize;
    const NUM_VARIABLES_ON_NEXT_STEP: usize;
    fn range_of_multiplicative_term() -> std::ops::Range<usize>;
    fn range_of_linear_terms() -> std::ops::Range<usize>;
    fn index_for_constant_term() -> usize;
    fn range_of_next_step_linear_terms() -> std::ops::Range<usize>;
    fn format_term<E: Engine>(instance: MainGateTerm<E>, padding: Variable) -> Result<(Vec<Variable>, Vec<E::Fr>), SynthesisError>;
}

pub trait GateEquation: GateEquationInternal
    + Sized
    + Clone
    + std::hash::Hash
    + std::default::Default 
{
    const HAS_NONTRIVIAL_CONSTANTS: bool;
    const NUM_CONSTANTS: usize;

    fn as_internal(&self) -> &dyn GateEquationInternal {
        self as &dyn GateEquationInternal
    }

    fn into_internal(self) -> Box<dyn GateEquationInternal> {
        Box::from(self) as Box<dyn GateEquationInternal>
    }

    fn static_description() -> &'static Self;

    fn output_constant_coefficients<E: Engine>() -> Vec<E::Fr>;
}

pub trait GateEquationInternal: Send 
    + Sync 
    + 'static 
    + std::any::Any 
    + std::fmt::Debug
{
    fn degree(&self) -> usize;
    fn num_constraints(&self) -> usize;
    fn get_constraint(&self) -> &LinearCombinationOfTerms;
    fn get_constraints(&self) -> &[LinearCombinationOfTerms];
}

impl std::hash::Hash for dyn GateEquationInternal {
    fn hash<H>(&self, state: &mut H) where H: std::hash::Hasher {
        self.type_id().hash(state);
        self.degree().hash(state);
        for t in self.get_constraints().iter() {
            t.hash(state);
        }
    }
}

impl PartialEq for dyn GateEquationInternal {
    fn eq(&self, other: &Self) -> bool {
        self.degree() == other.degree() &&
        self.get_constraints() == other.get_constraints()
    }
}

impl Eq for dyn GateEquationInternal {}

#[derive(Clone, Debug, Hash)]
pub struct Width4MainGateWithDNextEquation(pub [LinearCombinationOfTerms; 1]);

impl GateEquationInternal for Width4MainGateWithDNextEquation {
    fn degree(&self) -> usize {
        3
    }

    fn num_constraints(&self) -> usize {
        1
    }

    fn get_constraint(&self) -> &LinearCombinationOfTerms {
        &(self.0[0])
    }

    fn get_constraints(&self) -> &[LinearCombinationOfTerms] {
        &self.0[..]
    }
}

impl GateEquation for Width4MainGateWithDNextEquation {
    const HAS_NONTRIVIAL_CONSTANTS: bool = false;
    const NUM_CONSTANTS: usize = 7;

    // Width4MainGateWithDNextEquation is NOT generic, so this is fine
    // and safe since it's sync!
    fn static_description() -> &'static Self {
        static mut VALUE: Option<Width4MainGateWithDNextEquation> = None;
        static INIT: std::sync::Once = std::sync::Once::new();

        unsafe {
            INIT.call_once(||{
                VALUE = Some(Width4MainGateWithDNextEquation::default());
            });

            VALUE.as_ref().unwrap()
        }
    }

    fn output_constant_coefficients<E: Engine>() -> Vec<E::Fr> {
        vec![E::Fr::one(); 7]
    }
}

impl MainGateEquation for Width4MainGateWithDNextEquation {
    const NUM_LINEAR_TERMS: usize = 4;
    const NUM_VARIABLES: usize = 4;
    const NUM_VARIABLES_ON_NEXT_STEP: usize = 1;

    fn range_of_multiplicative_term() -> std::ops::Range<usize> {
        0..2
    }
    fn range_of_linear_terms() -> std::ops::Range<usize> {
        0..4
    }

    fn index_for_constant_term() -> usize {
        5
    }

    fn range_of_next_step_linear_terms() -> std::ops::Range<usize> {
        6..7
    }

    fn format_term<E: Engine>(mut instance: MainGateTerm<E>, padding: Variable) -> Result<(Vec<Variable>, Vec<E::Fr>), SynthesisError> {
        let mut flattened_variables = vec![padding; Self::NUM_VARIABLES];
        let mut flattened_coefficients = vec![E::Fr::zero(); 7];

        let allowed_linear = 4;
        let allowed_multiplications = 1;
        let allowed_constants = 1;

        debug_assert!(instance.num_constant_terms <= allowed_constants, "must not containt more constants than allowed");  
        debug_assert!(instance.num_multiplicative_terms <= allowed_multiplications, "must not containt more multiplications than allowed"); 
        debug_assert!(instance.terms.len() <= allowed_constants + allowed_multiplications + allowed_linear, "gate can not fit that many terms"); 

        if instance.num_multiplicative_terms != 0 {
            let index = instance.terms.iter().position(
                |t| {
                    match t {
                        ArithmeticTerm::Product(_, _) => true,
                        _ => false,
                    }
                }
            ).unwrap();

            let term = instance.terms.swap_remove(index);
            match term {
                ArithmeticTerm::Product(vars, coeff) => {
                    debug_assert_eq!(vars.len(), 2, "multiplicative terms must contain two variables");

                    flattened_variables[0] = vars[0];
                    flattened_variables[1] = vars[1];
                    flattened_coefficients[4] = coeff;
                },
                _ => {
                    unreachable!("must be multiplicative term");
                }
            }
        }

        if instance.num_constant_terms != 0 {
            let index = instance.terms.iter().position(
                |t| {
                    match t {
                        ArithmeticTerm::Constant(_) => true,
                        _ => false,
                    }
                }
            ).unwrap();

            let term = instance.terms.swap_remove(index);
            match term {
                ArithmeticTerm::Constant(coeff) => {
                    flattened_coefficients[5] = coeff;
                },
                _ => {
                    unreachable!("must be multiplicative term");
                }
            }
        }

        let mut idx = 0;
        for i in 0..flattened_variables.len() {
            if flattened_variables[i] == padding {
                break
            } else {
                idx += 1;
            }
        }

        // only additions left
        for term in instance.terms.into_iter() {
            loop {
                debug_assert!(idx < Self::NUM_VARIABLES, "somehow all variables are filled");

                if flattened_variables[idx] == padding {
                    break
                } else {
                    idx += 1;
                }
            }
            debug_assert!(idx < Self::NUM_VARIABLES, "somehow all variables are filled");
            match term {
                ArithmeticTerm::SingleVariable(var, coeff) => {
                    let index = flattened_variables.iter().position(
                        |&t| t == var
                    );
                    if let Some(index) = index {
                        // there is some variable there already,
                        flattened_coefficients[index] = coeff;
                    } else {
                        flattened_variables[idx] = var;
                        flattened_coefficients[idx] = coeff;
                        idx += 1;
                    }
                },
                _ => {
                    unreachable!("must be multiplicative term");
                }
            }
        }

        Ok((flattened_variables, flattened_coefficients))
    }
}

impl std::default::Default for Width4MainGateWithDNextEquation {
    fn default() -> Self {
        Self::get_equation()
    }
}

impl Width4MainGateWithDNextEquation {
    pub fn get_equation() -> Self {
        let mut terms: Vec<PolynomialMultiplicativeTerm> = Vec::with_capacity(7);
        // linear terms
        for i in 0..4 {
            // N * Q_n
            terms.push(
                PolynomialMultiplicativeTerm(
                    Coefficient::PlusOne,
                    vec![
                        PolynomialInConstraint::VariablesPolynomial(i, TimeDilation(0)), 
                        PolynomialInConstraint::SetupPolynomial("main gate of width 4", i, TimeDilation(0))
                    ]
                )
            );
        }

        // multiplication
        terms.push(
            PolynomialMultiplicativeTerm(
                Coefficient::PlusOne,
                vec![
                    PolynomialInConstraint::VariablesPolynomial(0, TimeDilation(0)), 
                    PolynomialInConstraint::VariablesPolynomial(1, TimeDilation(0)), 
                    PolynomialInConstraint::SetupPolynomial("main gate of width 4", 4, TimeDilation(0))
                ]
            )
        );

        // constant
        terms.push(
            PolynomialMultiplicativeTerm(
                Coefficient::PlusOne,
                vec![
                    PolynomialInConstraint::SetupPolynomial("main gate of width 4", 5, TimeDilation(0))
                ]
            )
        );

        terms.push(
            PolynomialMultiplicativeTerm(
                Coefficient::PlusOne,
                vec![
                    PolynomialInConstraint::VariablesPolynomial(3, TimeDilation(1)), 
                    PolynomialInConstraint::SetupPolynomial("main gate of width 4", 6, TimeDilation(0))
                ]
            )
        );

        Self([LinearCombinationOfTerms(terms)])
    }
}

fn check_gate_to_support_public_inputs<G: GateEquation>(gate: &G) -> bool {
    for t in gate.get_constraints() {
        for c in t.0.iter() {
            if c.1.len() != 1 {
                continue;
            }
            for s in c.1.iter() {
                match s {
                    PolynomialInConstraint::SetupPolynomial(..) => {
                        return true;
                    },
                    _ => {}
                }
            }
        }
    }

    false
}

fn has_access_to_next_step<G: GateEquation>(gate: &G) -> bool {
    for t in gate.get_constraints() {
        for c in t.0.iter() {
            for s in c.1.iter() {
                match s {
                    PolynomialInConstraint::VariablesPolynomial(_, TimeDilation(shift)) => {
                        if shift != &0usize {
                            return true;
                        }
                    },
                    PolynomialInConstraint::WitnessPolynomial(_, TimeDilation(shift)) => {
                        if shift != &0usize {
                            return true;
                        }
                    },
                    PolynomialInConstraint::SetupPolynomial(_, _, TimeDilation(shift)) => {
                        if shift != &0usize {
                            return true;
                        }
                    },
                }
            }
        }
    }

    false
}

fn max_addressed_state_poly<G: GateEquation>(gate: &G) -> Option<usize> {
    let mut max: Option<usize> = None;

    for t in gate.get_constraints() {
        for c in t.0.iter() {
            for s in c.1.iter() {
                match s {
                    PolynomialInConstraint::VariablesPolynomial(idx, _) => {
                        let new_max = match max.take() {
                            Some(value) => {
                                if value < *idx {
                                    Some(*idx)
                                } else {
                                    Some(value)
                                }
                            },
                            None => {
                                Some(*idx)
                            }
                        };

                        max = new_max;
                    },
                    _ => {}
                }
            }
        }
    }

    max
}

fn max_addressed_witness_poly<G: GateEquation>(gate: &G) -> Option<usize> {
    let mut max: Option<usize> = None;

    for t in gate.get_constraints() {
        for c in t.0.iter() {
            for s in c.1.iter() {
                match s {
                    PolynomialInConstraint::WitnessPolynomial(idx, _) => {
                        let new_max = match max.take() {
                            Some(value) => {
                                if value < *idx {
                                    Some(*idx)
                                } else {
                                    Some(value)
                                }
                            },
                            None => {
                                Some(*idx)
                            }
                        };

                        max = new_max;
                    },
                    _ => {}
                }
            }
        }
    }

    max
}

// fn max_addressed_setup_poly<G: GateEquation>(gate: &G) -> Option<(usize, &'static str)> {
//     let mut max: Option<usize> = None;

//     let mut setup_tag = None;

//     for t in gate.get_constraints() {
//         for c in t.0.iter() {
//             for s in c.0.iter() {
//                 match s {
//                     PolynomialInConstraint::SetupPolynomial(name, idx, _) => {
//                         let new_max = match max.take() {
//                             Some(value) => {
//                                 if value < *idx {
//                                     Some(*idx)
//                                 } else {
//                                     Some(value)
//                                 }
//                             },
//                             None => {
//                                 Some(*idx)
//                             }
//                         };

//                         max = new_max;
//                     },
//                     _ => {}
//                 }
//             }
//         }
//     }

//     max
// }

fn check_gate_is_allowed_for_params<E: Engine, P: PlonkConstraintSystemParams<E>, G: GateEquation>(
    gate: &G
) -> bool {
    let mut max_state = max_addressed_state_poly(gate);
    let mut max_witness = max_addressed_witness_poly(gate);
    // let max_setup = max_addressed_setup_poly(gate);

    let accesses_other_rows = has_access_to_next_step(gate);
    if accesses_other_rows && P::CAN_ACCESS_NEXT_TRACE_STEP == false {
        return false;
    }

    match max_state.take() {
        Some(m) => {
            if m > P::STATE_WIDTH {
                return false;
            }
        },
        _ => {}
    }

    match max_witness.take() {
        Some(m) => {
            if m > P::WITNESS_WIDTH {
                return false;
            }
        },
        _ => {}
    }

    true
}

pub trait PlonkConstraintSystemParams<E: Engine> {
    const STATE_WIDTH: usize;
    const WITNESS_WIDTH: usize;
    const HAS_WITNESS_POLYNOMIALS: bool;
    const HAS_CUSTOM_GATES: bool;
    const CAN_ACCESS_NEXT_TRACE_STEP: bool;
}

pub trait ConstraintSystem<E: Engine> {
    type Params: PlonkConstraintSystemParams<E>;
    type MainGate: MainGateEquation;

    // allocate a variable
    fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>;

    // allocate an input variable
    fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>;

    fn new_single_gate_for_trace_step<G: GateEquation>(&mut self, 
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

    fn allocate_main_gate(&mut self, gate: MainGateTerm<E>) -> Result<(), SynthesisError> {
        let (vars, coeffs) = Self::MainGate::format_term(gate, Self::get_dummy_variable())?;

        let mg = Self::MainGate::static_description();

        self.new_single_gate_for_trace_step(
            mg,
            &coeffs,
            &vars,
            &[]
        )
    }

    fn begin_gates_batch_for_step(&mut self) -> Result<(), SynthesisError>;
    fn new_gate_in_batch<G: GateEquation>(&mut self, 
        equation: &G,
        coefficients_assignments: &[E::Fr],
        variables_assignments: &[Variable],
        witness_assignments: &[E::Fr]
    ) -> Result<(), SynthesisError>;
    fn end_gates_batch_for_step(&mut self) -> Result<(), SynthesisError>;

    fn get_value(&self, _variable: Variable) -> Result<E::Fr, SynthesisError> { 
        Err(SynthesisError::AssignmentMissing)
    }

    fn get_dummy_variable() -> Variable;
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

use crate::plonk::polynomials::*;

// pub struct PolynomialStorage<E: Engine> {
//     pub state_map: std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Values>>,
//     pub witness_map: std::collections::HashMap<PolyIdentifier,Polynomial<E::Fr, Values>>,
//     pub setup_map: std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Values>>,
// }

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
            PolynomialInConstraint::VariablesPolynomial(_, _) => {
                unreachable!("should not try to get value of the state polynomial, get variable first instead");
            },
            PolynomialInConstraint::SetupPolynomial(gate_descr, idx, TimeDilation(dilation)) => {
                let final_index = n + dilation;
                let identifier = PolyIdentifier::SetupPolynomial(gate_descr, *idx);
                let value = *self.setup_map
                    .get(&identifier)
                    .ok_or(SynthesisError::AssignmentMissing)?
                    .get(final_index)
                    .ok_or(SynthesisError::AssignmentMissing)?;

                Ok(value)
            },
            PolynomialInConstraint::WitnessPolynomial(_, _) => {
                unimplemented!()
            }
        }
    }

    pub fn get_variable(&self, poly: &PolynomialInConstraint, n: usize) -> Result<Variable, SynthesisError> {
        match poly {
            PolynomialInConstraint::VariablesPolynomial(idx, TimeDilation(dilation)) => {
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

pub struct GateDensityStorage(pub std::collections::HashMap<Box<dyn GateEquationInternal>, BitVec>);

impl GateDensityStorage {
    pub fn new() -> Self {
        Self(std::collections::HashMap::new())
    }
}

pub struct GateConstantCoefficientsStorage<E: Engine>(pub std::collections::HashMap<Box<dyn GateEquationInternal>, Vec<E::Fr>>);

impl<E: Engine> GateConstantCoefficientsStorage<E> {
    pub fn new() -> Self {
        Self(std::collections::HashMap::new())
    }
}

pub struct TrivialAssembly<E: Engine, P: PlonkConstraintSystemParams<E>, MG: MainGateEquation> {
    pub storage: PolynomialStorage<E>,
    pub n: usize,
    pub max_constraint_degree: usize,
    pub main_gate: MG,
    pub input_assingments: Vec<E::Fr>,
    pub aux_assingments: Vec<E::Fr>,
    pub num_inputs: usize,
    pub num_aux: usize,
    pub trace_step_for_batch: Option<usize>,
    pub constraints: std::collections::HashSet<Box<dyn GateEquationInternal>>,
    pub gate_internal_coefficients: GateConstantCoefficientsStorage<E>,
    pub gate_density: GateDensityStorage,
    _marker: std::marker::PhantomData<P>
}

impl<E: Engine, P: PlonkConstraintSystemParams<E>, MG: MainGateEquation> ConstraintSystem<E> for TrivialAssembly<E, P, MG> {
    type Params = P;
    type MainGate = MG;

    // allocate a variable
    fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {
        let value = value()?;

        self.num_aux += 1;
        let index = self.num_aux;
        self.aux_assingments.push(value);

        // println!("Allocated variable Aux({}) with value {}", index, value);

        Ok(Variable(Index::Aux(index)))
    }

    // allocate an input variable
    fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {
        let value = value()?;

        self.num_inputs += 1;
        let index = self.num_inputs;
        self.input_assingments.push(value);

        let input_var = Variable(Index::Input(index));

        // TODO: add gate
        // self.n += 1;

        Ok(input_var)
    }

    fn get_main_gate(&self) -> &MG {
        &self.main_gate
    }

    fn begin_gates_batch_for_step(&mut self) -> Result<(), SynthesisError> {
        debug_assert!(self.trace_step_for_batch.is_none());
        let n = self.n;
        self.trace_step_for_batch = Some(n);

        Ok(())
    }

    fn new_gate_in_batch<G: GateEquation>(&mut self, 
        gate: &G,
        coefficients_assignments: &[E::Fr],
        variables_assignments: &[Variable],
        witness_assignments: &[E::Fr]
    ) -> Result<(), SynthesisError> {
        // check that gate is ok for config
        debug_assert!(check_gate_is_allowed_for_params::<E, P, G>(&gate), format!("supplied params do not work with gate {:?}", gate));

        let n = self.trace_step_for_batch.unwrap();
        let dummy = Self::get_dummy_variable();
        let zero = E::Fr::zero();

        let mut coeffs_it = coefficients_assignments.iter();

        let mut setup_index: Option<(&'static str, usize)> = None;
        for t in gate.get_constraints() {
            for c in t.0.iter() {
                for s in c.1.iter() {
                    match s {
                        PolynomialInConstraint::SetupPolynomial(name, idx, _) => {
                            setup_index = Some((name, *idx));
                        },
                        _ => {}
                    }

                    match setup_index.take() {
                        Some((name, idx)) => {
                            let key = PolyIdentifier::SetupPolynomial(name, idx);
                            let poly_ref = self.storage.setup_map.entry(key).or_insert(vec![]);
                            if poly_ref.len() < n {
                                poly_ref.resize(n, E::Fr::zero());
                            }
                            poly_ref.push(*coeffs_it.next().unwrap_or(&zero));
                        },
                        _ => {}
                    }
                }
            }
        }

        debug_assert!(coeffs_it.next().is_none(), "must consume all the coefficients for gate");

        let mut variable_index: Option<usize> = None;

        let mut variable_it = variables_assignments.iter();

        // go through all used variables to place them into the STATE
        for t in gate.get_constraints() {
            for c in t.0.iter() {
                for s in c.1.iter() {
                    match s {
                        PolynomialInConstraint::VariablesPolynomial(idx, TimeDilation(0)) => {
                            variable_index = Some(*idx);
                        }
                        PolynomialInConstraint::VariablesPolynomial(_, TimeDilation(_)) => {
                            // gate can only have power over the current step
                        },
                        _ => {}
                    }

                    match variable_index.take() {
                        Some(idx) => {
                            let key = PolyIdentifier::VariablesPolynomial(idx);
                            let poly_ref = self.storage.state_map.entry(key).or_insert(vec![]);
                            if poly_ref.len() < n {
                                poly_ref.resize(n, dummy);
                            } else if poly_ref.len() == n {
                                // we consume variable only ONCE
                                let var = *variable_it.next().unwrap_or(&dummy);
                                poly_ref.push(var);
                            }
                        },
                        _ => {}
                    }
                }
            }
        }

        debug_assert!(variable_it.next().is_none(), "must consume all variables for gate");

        let mut witness_it = witness_assignments.iter();

        let mut witness_index: Option<usize> = None;

        // go through all used variables to place them into the STATE
        for t in gate.get_constraints() {
            for c in t.0.iter() {
                for s in c.1.iter() {
                    match s {
                        PolynomialInConstraint::WitnessPolynomial(idx, TimeDilation(0)) => {
                            witness_index = Some(*idx);
                        },
                        _ => {}
                    }

                    match witness_index.take() {
                        Some(idx) => {
                            let key = PolyIdentifier::VariablesPolynomial(idx);
                            let poly_ref = self.storage.witness_map.entry(key).or_insert(vec![]);
                            if poly_ref.len() < n {
                                poly_ref.resize(n, E::Fr::zero());
                            } 
                            poly_ref.push(*witness_it.next().unwrap_or(&zero));
                        },
                        _ => {}
                    }
                }
            }
        }

        debug_assert!(witness_it.next().is_none(), "must consume all variables for gate");

        if !self.constraints.contains(gate.as_internal() as &dyn GateEquationInternal) {
            self.constraints.insert(gate.clone().into_internal());
            let gate_constants = G::output_constant_coefficients::<E>();
            self.gate_internal_coefficients.0.insert(Box::from(MG::default()), gate_constants);
        }        

        if let Some(tracker) = self.gate_density.0.get_mut(gate.as_internal() as &dyn GateEquationInternal) {
            if tracker.len() != n {
                let padding = n - tracker.len();
                tracker.grow(padding, false);
            }
            tracker.push(true);
            debug_assert_eq!(n+1, tracker.len());
        } else {
            self.gate_density.0.insert(gate.clone().into_internal(), BitVec::new());
            let tracker = self.gate_density.0.get_mut(gate.as_internal() as &dyn GateEquationInternal).unwrap();
            tracker.grow(n, false);
            tracker.push(true);
        }

        Ok(())
    }

    fn end_gates_batch_for_step(&mut self) -> Result<(), SynthesisError> {
        debug_assert!(self.trace_step_for_batch.is_some());
        let n = self.trace_step_for_batch.take().unwrap();
        debug_assert_eq!(n, self.n, "invalid batch id");

        self.n += 1;

        Ok(())
    }

    fn get_value(&self, var: Variable) -> Result<E::Fr, SynthesisError> {
        let value = match var {
            Variable(Index::Aux(0)) => {
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
}

impl<E: Engine, P: PlonkConstraintSystemParams<E>, MG: MainGateEquation> TrivialAssembly<E, P, MG> {
    pub fn new() -> Self {
        let mut tmp = Self {
            n: 0,

            storage: PolynomialStorage::new(),

            max_constraint_degree: 0,

            num_inputs: 0,
            num_aux: 0,

            input_assingments: vec![],
            aux_assingments: vec![],

            main_gate: MG::default(),

            trace_step_for_batch: None,

            constraints: std::collections::HashSet::new(),
            gate_internal_coefficients: GateConstantCoefficientsStorage::<E>::new(),

            gate_density: GateDensityStorage::new(),

            _marker: std::marker::PhantomData
        };

        tmp.max_constraint_degree = tmp.main_gate.degree();
        tmp.constraints.insert(Box::from(MG::default()));

        let gate_constants = MG::output_constant_coefficients::<E>();
        tmp.gate_internal_coefficients.0.insert(Box::from(MG::default()), gate_constants);

        assert!(check_gate_to_support_public_inputs(&tmp.main_gate), "default gate must support making public inputs");

        tmp
    }

    // return variable that is not in a constraint formally, but has some value
    fn dummy_variable() -> Variable {
        Variable(Index::Aux(0))
    }

    pub fn is_satisfied(&self) -> bool {
        // expect a small number of inputs

        // TODO: handle public inputs

        let one = E::Fr::one();
        let mut minus_one = E::Fr::one();
        minus_one.negate();

        for (gate_type, density) in self.gate_density.0.iter() {
            let constraints = gate_type.as_ref().get_constraints();
            let constants = self.gate_internal_coefficients.0.get(gate_type.as_ref()).unwrap();
            let mut constants_iter = constants.iter();

            for (n, is_applicable) in density.iter().enumerate() {
                if is_applicable == false {
                    continue;
                }

                for constraint in constraints.iter() {
                    let mut constraint_value = E::Fr::zero();
                    for term in constraint.0.iter() {
                        let mut base = match term.0 {
                            Coefficient::PlusOne => one,
                            Coefficient::MinusOne => minus_one,
                            Coefficient::Other => *constants_iter.next().unwrap()
                        };

                        for poly in term.1.iter() {
                            let value = match poly {
                                PolynomialInConstraint::VariablesPolynomial(_, TimeDilation(dilation)) => {
                                    if n == self.n-1 && *dilation > 0 {
                                        continue;
                                    }
                                    let variable = self.storage.get_variable(poly, n).expect(&format!("must get a variable for poly {:?} for gate {}", poly, n));
                                    let value = self.get_value(variable).expect("must get a state variable value");

                                    value
                                },
                                PolynomialInConstraint::SetupPolynomial(_, _, TimeDilation(dilation)) => {
                                    if n == self.n-1 && *dilation > 0 {
                                        continue;
                                    }

                                    let value = self.storage.get_value(poly, n).expect(&format!("must get a setup value for poly {:?} for gate {}", poly, n));
                                    
                                    value
                                },
                                PolynomialInConstraint::WitnessPolynomial(_, TimeDilation(dilation)) => {
                                    if n == self.n-1 && *dilation > 0 {
                                        continue;
                                    }

                                    let value = self.storage.get_value(poly, n).expect(&format!("must get a witness value for poly {:?} for gate {}", poly, n));
                                    
                                    value
                                }
                            };

                            base.mul_assign(&value);
                        }

                        constraint_value.add_assign(&base);
                    }

                    if !constraint_value.is_zero() {
                        println!("Unsatisfied at gate {}", n);
                        println!("Constraint value = {}", constraint_value);
                        println!("Gate {:?}", gate_type);
                        return false;
                    }
                }
            }
        }

        true
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::pairing::Engine;
    use crate::pairing::ff::PrimeField;

    struct TestCircuit4<E:Engine>{
        _marker: PhantomData<E>
    }

    // impl<E: Engine> Circuit<E> for TestCircuit4<E> {
    //     fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
    //         let main_gate = CS::MainGate::default();
    //         // let main_gate = Width4MainGateWithDNextEquation::default();

    //         let a = cs.alloc(|| {
    //             Ok(E::Fr::from_str("10").unwrap())
    //         })?;

    //         println!("A = {:?}", a);

    //         let b = cs.alloc(|| {
    //             Ok(E::Fr::from_str("20").unwrap())
    //         })?;

    //         println!("B = {:?}", b);

    //         let c = cs.alloc(|| {
    //             Ok(E::Fr::from_str("200").unwrap())
    //         })?;

    //         println!("C = {:?}", c);

    //         let d = cs.alloc(|| {
    //             Ok(E::Fr::from_str("100").unwrap())
    //         })?;

    //         println!("D = {:?}", d);

    //         let zero = E::Fr::zero();

    //         let one = E::Fr::one();

    //         let mut two = one;
    //         two.double();

    //         let mut negative_one = one;
    //         negative_one.negate();

    //         let dummy = CS::get_dummy_variable();

    //         cs.new_single_gate_for_trace_step(
    //             &main_gate, 
    //             &[two, negative_one, zero, zero, zero, zero, zero],
    //             &[a, b, dummy, dummy], 
    //             &[]
    //         )?;

    //         // 10b - c = 0
    //         let ten = E::Fr::from_str("10").unwrap();

    //         cs.new_single_gate_for_trace_step(
    //             &main_gate, 
    //             &[ten, negative_one, zero, zero, zero, zero, zero],
    //             &[b, c, dummy, dummy], 
    //             &[]
    //         )?;

    //         // c - a*b == 0 

    //         cs.new_single_gate_for_trace_step(
    //             &main_gate, 
    //             &[zero, zero, zero, negative_one, one, zero, zero],
    //             &[a, b, dummy, c], 
    //             &[]
    //         )?;

    //         // 10a + 10b - c - d == 0

    //         cs.new_single_gate_for_trace_step(
    //             &main_gate, 
    //             &[ten, ten, negative_one, negative_one, zero, zero, zero],
    //             &[a, b, c, d], 
    //             &[]
    //         )?;

    //         Ok(())
    //     }
    // }

    impl<E: Engine> Circuit<E> for TestCircuit4<E> {
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let a = cs.alloc(|| {
                Ok(E::Fr::from_str("10").unwrap())
            })?;

            println!("A = {:?}", a);

            let b = cs.alloc(|| {
                Ok(E::Fr::from_str("20").unwrap())
            })?;

            println!("B = {:?}", b);

            let c = cs.alloc(|| {
                Ok(E::Fr::from_str("200").unwrap())
            })?;

            println!("C = {:?}", c);

            let d = cs.alloc(|| {
                Ok(E::Fr::from_str("100").unwrap())
            })?;

            println!("D = {:?}", d);

            let one = E::Fr::one();

            let mut two = one;
            two.double();

            let mut negative_one = one;
            negative_one.negate();

            // 2a - b = 0

            let two_a = ArithmeticTerm::from_variable_and_coeff(a, two);
            let minus_b = ArithmeticTerm::from_variable_and_coeff(b, negative_one);
            let mut term = MainGateTerm::new();
            term.add_assign(two_a);
            term.add_assign(minus_b);

            cs.allocate_main_gate(term)?;

            // c - a*b == 0 

            let mut ab_term = ArithmeticTerm::from_variable(a).mul_by_variable(b);
            ab_term.scale(&negative_one);
            let c_term = ArithmeticTerm::from_variable(c);
            let mut term = MainGateTerm::new();
            term.add_assign(c_term);
            term.add_assign(ab_term);

            cs.allocate_main_gate(term)?;

            // d - 100 == 0 

            let hundred = ArithmeticTerm::constant(E::Fr::from_str("100").unwrap());
            let d_term = ArithmeticTerm::from_variable(d);
            let mut term = MainGateTerm::new();
            term.add_assign(d_term);
            term.sub_assign(hundred);

            cs.allocate_main_gate(term)?;

            Ok(())
        }
    }

    #[test]
    fn test_trivial_circuit_with_gate_agnostic_cs() {
        use crate::pairing::bn256::{Bn256, Fr};
        use crate::worker::Worker;

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextEquation>::new();

        let circuit = TestCircuit4::<Bn256> {
            _marker: PhantomData
        };

        circuit.synthesize(&mut assembly).expect("must work");

        assert!(assembly.constraints.len() == 1);

        // println!("Assembly state polys = {:?}", assembly.storage.state_map);

        // println!("Assembly setup polys = {:?}", assembly.storage.setup_map);    

        println!("Assembly contains {} constraints", assembly.n);
        
        assert!(assembly.is_satisfied());
    }
}