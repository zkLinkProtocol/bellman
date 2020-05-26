use crate::pairing::ff::{Field};
use crate::pairing::{Engine};
use crate::bit_vec::BitVec;

use crate::{SynthesisError};
use std::marker::PhantomData;

use crate::worker::Worker;
use crate::plonk::domains::*;
use crate::plonk::polynomials::*;

pub use crate::plonk::cs::variable::*;
use crate::plonk::better_cs::utils::*;
pub use super::lookup_tables::*;

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
    fn linearizes_over(&self) -> Vec<PolyIdentifier>;
    fn needs_opened_for_linearization(&self) -> Vec<PolynomialInConstraint>;
    // fn compute_linearization_contribution(&self, values: &[E::Fr]) -> Vec<E::Fr> {
    //     vec![]
    // } 
    fn num_quotient_terms(&self) -> usize;
    fn verify_on_row(&self, row: usize, poly_storage: &AssembledPolynomialStorage<E>, last_row: bool) -> E::Fr;
    fn contribute_into_quotient(
        &self, 
        poly_storage: &AssembledPolynomialStorage<E>,
        challenges: &[E::Fr],
        lde_factor: usize,
    ) -> Result<Polynomial<E::Fr, Values>, SynthesisError>;
    fn put_public_inputs_into_selector_id(&self) -> Option<usize>;
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
    fn range_of_multiplicative_term() -> std::ops::Range<usize>;
    fn range_of_linear_terms() -> std::ops::Range<usize>;
    fn index_for_constant_term() -> usize;
    fn range_of_next_step_linear_terms() -> std::ops::Range<usize>;
    fn format_term(instance: MainGateTerm<E>, padding: Variable) -> Result<(Vec<Variable>, Vec<E::Fr>), SynthesisError>;
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

    pub fn len_without_constant(&self) -> usize {
        self.terms.len()
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


#[derive(Clone, Debug, Hash, Default)]
pub struct Width4MainGateWithDNext;

impl<E: Engine> GateInternal<E> for Width4MainGateWithDNext {
    fn name(&self) -> &'static str {
        "main gate of width 4"
    }

    fn degree(&self) -> usize {
        3
    }

    fn can_include_public_inputs(&self) -> bool {
        true
    }

    fn all_queried_polynomials(&self) -> Vec<PolynomialInConstraint> {
        vec![
            PolynomialInConstraint::SetupPolynomial("main gate of width 4", 0, TimeDilation(0)),
            PolynomialInConstraint::SetupPolynomial("main gate of width 4", 1, TimeDilation(0)),
            PolynomialInConstraint::SetupPolynomial("main gate of width 4", 2, TimeDilation(0)),
            PolynomialInConstraint::SetupPolynomial("main gate of width 4", 3, TimeDilation(0)),
            PolynomialInConstraint::SetupPolynomial("main gate of width 4", 4, TimeDilation(0)),
            PolynomialInConstraint::SetupPolynomial("main gate of width 4", 5, TimeDilation(0)),
            PolynomialInConstraint::SetupPolynomial("main gate of width 4", 6, TimeDilation(0)),

            PolynomialInConstraint::VariablesPolynomial(0, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(1, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(2, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(3, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(3, TimeDilation(1)),
        ]
    }

    fn setup_polynomials(&self) -> Vec<PolyIdentifier> {
        vec![
            PolyIdentifier::SetupPolynomial("main gate of width 4", 0),
            PolyIdentifier::SetupPolynomial("main gate of width 4", 1),
            PolyIdentifier::SetupPolynomial("main gate of width 4", 2),
            PolyIdentifier::SetupPolynomial("main gate of width 4", 3),
            PolyIdentifier::SetupPolynomial("main gate of width 4", 4),
            PolyIdentifier::SetupPolynomial("main gate of width 4", 5),
            PolyIdentifier::SetupPolynomial("main gate of width 4", 6),
        ]
    }

    fn variable_polynomials(&self) -> Vec<PolyIdentifier> {
        vec![
            PolyIdentifier::VariablesPolynomial(0),
            PolyIdentifier::VariablesPolynomial(1),
            PolyIdentifier::VariablesPolynomial(2),
            PolyIdentifier::VariablesPolynomial(3),
        ]
    }

    fn benefits_from_linearization(&self) -> bool {
        true
    }

    fn linearizes_over(&self) -> Vec<PolyIdentifier> {
        vec![
            PolyIdentifier::SetupPolynomial("main gate of width 4", 0),
            PolyIdentifier::SetupPolynomial("main gate of width 4", 1),
            PolyIdentifier::SetupPolynomial("main gate of width 4", 2),
            PolyIdentifier::SetupPolynomial("main gate of width 4", 3),
            PolyIdentifier::SetupPolynomial("main gate of width 4", 4),
            PolyIdentifier::SetupPolynomial("main gate of width 4", 5),
            PolyIdentifier::SetupPolynomial("main gate of width 4", 6),
        ]
    }

    fn needs_opened_for_linearization(&self) -> Vec<PolynomialInConstraint> {
        vec![
            PolynomialInConstraint::VariablesPolynomial(0, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(1, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(2, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(3, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(3, TimeDilation(1)),
        ]
    }

    fn num_quotient_terms(&self) -> usize {
        1
    }

    fn verify_on_row(&self, row: usize, poly_storage: &AssembledPolynomialStorage<E>, last_row: bool) -> E::Fr {
        let q_a = poly_storage.get_poly_at_step(PolyIdentifier::SetupPolynomial("main gate of width 4", 0), row);
        let q_b = poly_storage.get_poly_at_step(PolyIdentifier::SetupPolynomial("main gate of width 4", 1), row);
        let q_c = poly_storage.get_poly_at_step(PolyIdentifier::SetupPolynomial("main gate of width 4", 2), row);
        let q_d = poly_storage.get_poly_at_step(PolyIdentifier::SetupPolynomial("main gate of width 4", 3), row);
        let q_m = poly_storage.get_poly_at_step(PolyIdentifier::SetupPolynomial("main gate of width 4", 4), row);
        let q_const = poly_storage.get_poly_at_step(PolyIdentifier::SetupPolynomial("main gate of width 4", 5), row);
        let q_d_next = poly_storage.get_poly_at_step(PolyIdentifier::SetupPolynomial("main gate of width 4", 6), row);

        // println!("{}*A + {}*B + {}*C + {}*D + {} + {}*A*A + {}*D_next", q_a, q_b, q_c, q_d, q_const, q_m, q_d_next);
        let a_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(0), row);
        let b_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(1), row);
        let c_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(2), row);
        let d_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(3), row);
        let d_next_value = if last_row == false {
            Some(poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(3), row+1))
        } else {
            None
        }; 

        // println!("A = {}, B = {}, C = {}, D = {}, D_Next = {:?}", a_value, b_value, c_value, d_value, d_next_value);

        let mut total = E::Fr::zero();

        for (q, v) in [a_value, b_value, c_value, d_value].iter()
                    .zip([q_a, q_b, q_c, q_d].iter())
        {
            let mut tmp = *q;
            tmp.mul_assign(v);
            total.add_assign(&tmp);
        }

        total.add_assign(&q_const);

        let mut tmp = q_m;
        tmp.mul_assign(&a_value);
        tmp.mul_assign(&b_value);
        total.add_assign(&tmp);

        if last_row == false {
            let mut tmp = d_next_value.expect("must be able to get d_next");
            tmp.mul_assign(&q_d_next);

            total.add_assign(&tmp);
        } else {
            assert!(q_d_next.is_zero());
        }

        total
    }

    fn contribute_into_quotient(
        &self, 
        poly_storage: &AssembledPolynomialStorage<E>,
        challenges: &[E::Fr],
        lde_factor: usize,
    ) -> Result<Polynomial<E::Fr, Values>, SynthesisError> {
        unimplemented!()
    }

    fn put_public_inputs_into_selector_id(&self) -> Option<usize> {
        Some(5)
    }
}

impl<E: Engine> Gate<E> for Width4MainGateWithDNext {

}

impl<E: Engine> MainGate<E> for Width4MainGateWithDNext {
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

    fn format_term(mut instance: MainGateTerm<E>, padding: Variable) -> Result<(Vec<Variable>, Vec<E::Fr>), SynthesisError> {
        let mut flattened_variables = vec![padding; 4];
        let mut flattened_coefficients = vec![E::Fr::zero(); 7];
        let mut bitmap = SimpleBitmap::new();

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
                    bitmap.set(0);
                    bitmap.set(1);
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

        // only additions left
        for term in instance.terms.into_iter() {
            match term {
                ArithmeticTerm::SingleVariable(var, coeff) => {
                    let index = flattened_variables.iter().position(
                        |&t| t == var
                    );
                    if let Some(index) = index {
                        // there is some variable there already,
                        flattened_coefficients[index] = coeff;
                    } else {
                        let idx = bitmap.get_next_unused();
                        flattened_variables[idx] = var;
                        flattened_coefficients[idx] = coeff;
                        bitmap.set(idx);
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

struct SimpleBitmap(u64, usize);
impl SimpleBitmap {
    fn new() -> Self {
        Self(0u64, 0)
    }

    fn get_next_unused(&mut self) -> usize {
        for i in 0..64 {
            if self.get(i) == false {
                return i;
            }
        }

        unreachable!()
    }

    fn get(&self, idx: usize) -> bool{
        1u64 << idx & self.0 > 0
    }

    fn set(&mut self, idx: usize) {
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

    fn get_value(&self, _variable: Variable) -> Result<E::Fr, SynthesisError> { 
        Err(SynthesisError::AssignmentMissing)
    }

    fn get_dummy_variable() -> Variable;

    fn get_explicit_zero(&mut self) -> Result<Variable, SynthesisError>;
    fn get_explicit_one(&mut self) -> Result<Variable, SynthesisError>;

    fn add_table(&mut self, table: LookupTableApplication<E>) -> Result<(), SynthesisError>;
    fn get_table(&self, functional_name: &str) -> Result<Arc<LookupTableApplication<E>>, SynthesisError>; 

    fn add_multitable(&mut self, table: MultiTableApplication<E>) -> Result<(), SynthesisError>;
    fn get_multitable(&self, functional_name: &str) -> Result<Arc<MultiTableApplication<E>>, SynthesisError>; 

    fn apply_single_lookup_gate(&mut self, variables: &[Variable], gate: Arc<LookupTableApplication<E>>) -> Result<(), SynthesisError>;
    fn apply_multi_lookup_gate(&mut self, variables: &[Variable], gate: Arc<MultiTableApplication<E>>) -> Result<(), SynthesisError>;
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

pub struct AssembledPolynomialStorage<E: Engine> {
    pub state_map: std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Values>>,
    pub witness_map: std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Values>>,
    pub setup_map: std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Values>>,
    pub is_bitreversed: bool,
    pub lde_factor: usize
}

impl<E: Engine> AssembledPolynomialStorage<E> {
    pub fn get_poly(&self, id: PolyIdentifier) -> &Polynomial<E::Fr, Values> {
        match id {
            p @ PolyIdentifier::VariablesPolynomial(..) => {
                self.state_map.get(&p).expect("poly must exist")
            },
            p @ PolyIdentifier::WitnessPolynomial(..) => {
                self.witness_map.get(&p).expect("poly must exist")
            },
            p @ PolyIdentifier::SetupPolynomial(..) => {
                self.setup_map.get(&p).expect("poly must exist")
            }
        }
    }
    pub fn get_poly_at_step(&self, id: PolyIdentifier, step: usize) -> E::Fr {
        assert!(self.is_bitreversed == false);
        assert!(self.lde_factor == 1);
        let p = self.get_poly(id);
        p.as_ref()[step]
    }
}

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

pub struct TrivialAssembly<E: Engine, P: PlonkConstraintSystemParams<E>, MG: MainGate<E>> {
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
    // pub gate_internal_coefficients: GateConstantCoefficientsStorage<E>,
    pub sorted_setup_polynomial_ids: Vec<PolyIdentifier>,
    pub sorted_gates: Vec<Box<dyn GateInternal<E>>>,
    // pub sorted_gate_constants: Vec<Vec<E::Fr>>,
    pub aux_gate_density: GateDensityStorage<E>,
    pub explicit_zero_variable: Option<Variable>,
    pub explicit_one_variable: Option<Variable>,

    pub tables: Vec<Arc<LookupTableApplication<E>>>,
    pub multitables: Vec<Arc<MultiTableApplication<E>>>,
    pub table_selectors: std::collections::HashMap<String, BitVec>,
    pub multitable_selectors: std::collections::HashMap<String, BitVec>,
    pub table_ids_poly: Vec<E::Fr>,
    pub individual_table_entries: std::collections::HashMap<String, Vec<Vec<E::Fr>>>,
    pub individual_multitable_entries: std::collections::HashMap<String, Vec<Vec<E::Fr>>>,
    pub known_table_ids: Vec<E::Fr>,

    _marker: std::marker::PhantomData<P>
}

impl<E: Engine, P: PlonkConstraintSystemParams<E>, MG: MainGate<E>> ConstraintSystem<E> for TrivialAssembly<E, P, MG> {
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
            witness_assignments
        )?;

        self.add_gate_into_list(gate);

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

    fn get_explicit_zero(&mut self) -> Result<Variable, SynthesisError> {
        if let Some(var) = self.explicit_zero_variable {
            return Ok(var);
        }

        let zero = self.alloc(|| Ok(E::Fr::zero()))?;

        self.explicit_zero_variable = Some(zero);

        Ok(zero)
    }

    fn get_explicit_one(&mut self) -> Result<Variable, SynthesisError> {
        if let Some(var) = self.explicit_one_variable {
            return Ok(var);
        }

        let one = self.alloc(|| Ok(E::Fr::one()))?;

        self.explicit_one_variable = Some(one);

        Ok(one)
    }

    fn add_table(&mut self, table: LookupTableApplication<E>) -> Result<(), SynthesisError> {
        assert!(table.applies_over().len() == 3, "only support tables of width 3");
        assert!(table.can_be_combined(), "can only add tables that are combinable");
        assert!(!self.known_table_ids.contains(&table.table_id()));
        let table_name = table.name();
        let table_id = table.table_id();
        self.tables.push(Arc::from(table));
        self.individual_table_entries.insert(table_name.clone(), vec![]);
        self.table_selectors.insert(table_name, BitVec::new());
        self.known_table_ids.push(table_id);

        Ok(())
    }

    fn get_table(&self, name: &str) -> Result<Arc<LookupTableApplication<E>>, SynthesisError> {
        for t in self.tables.iter() {
            if t.name() == name {
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

    fn apply_single_lookup_gate(&mut self, variables: &[Variable], table: Arc<LookupTableApplication<E>>) -> Result<(), SynthesisError> {
        self.num_aux_gates += 1;
        let n = self.num_aux_gates;

        debug_assert!(self.tables.contains(&table));

        let table_name = table.name();

        // we need to:
        // - mark that this table applies at this row
        // - add values into the list to later on make a sorted polynomial

        // make zero-enumerated index
        let n = n - 1;

        let tracker = self.table_selectors.get_mut(&table_name).unwrap();
        if tracker.len() != n {
            let padding = n - tracker.len();
            tracker.grow(padding, false);
        }
        tracker.push(true);
        debug_assert_eq!(n+1, tracker.len());

        let mut table_entries = Vec::with_capacity(table.applies_over().len());
        for v in variables.iter() {
            if let Ok(value) = self.get_value(*v) {
                table_entries.push(value);
            } else {
                panic!("value must exist");
            }
        }

        let entries = self.individual_table_entries.get_mut(&table_name).unwrap();
        assert_eq!(variables.len(), table.applies_over().len());

        assert!(table.is_valid_entry(&table_entries));

        self.table_ids_poly.resize(n, E::Fr::zero());
        self.table_ids_poly.push(table.table_id());

        entries.push(table_entries);


        Ok(())
    }
    
    fn apply_multi_lookup_gate(&mut self, variables: &[Variable], table: Arc<MultiTableApplication<E>>) -> Result<(), SynthesisError> {
        let n = self.trace_step_for_batch.expect("may only add table constraint in a transaction");
        // make zero-enumerated index
        let n = n - 1;

        let table_name = table.functional_name();
        let tracker = self.multitable_selectors.get_mut(&table_name).unwrap();
        if tracker.len() != n {
            let padding = n - tracker.len();
            tracker.grow(padding, false);
        }
        tracker.push(true);
        debug_assert_eq!(n+1, tracker.len());

        let mut table_entries = Vec::with_capacity(table.applies_over().len());
        for v in variables.iter() {
            if let Ok(value) = self.get_value(*v) {
                table_entries.push(value);
            } else {
                panic!("value must exist");
            }
        }

        let entries = self.individual_table_entries.get_mut(&table_name).unwrap();
        assert_eq!(variables.len(), table.applies_over().len());

        assert!(table.is_valid_entry(&table_entries));

        self.table_ids_poly.resize(n, E::Fr::zero());
        self.table_ids_poly.push(table.table_id());

        entries.push(table_entries);


        Ok(())
    }
}

impl<E: Engine, P: PlonkConstraintSystemParams<E>, MG: MainGate<E>> TrivialAssembly<E, P, MG> {
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

        let mut coeffs_it = coefficients_assignments.iter();

        for setup_poly in gate.setup_polynomials().into_iter() {
            let poly_ref = storage.setup_map.entry(setup_poly).or_insert(vec![]);
            if poly_ref.len() < n {
                poly_ref.resize(n, E::Fr::zero());
            }
            poly_ref.push(*coeffs_it.next().unwrap_or(&zero));
        }

        debug_assert!(coeffs_it.next().is_none(), "must consume all the coefficients for gate");

        let mut variable_it = variables_assignments.iter();

        for var_poly in gate.variable_polynomials().into_iter() {
            let poly_ref = storage.state_map.entry(var_poly).or_insert(vec![]);
            if poly_ref.len() < n {
                poly_ref.resize(n, dummy);
            } else if poly_ref.len() == n {
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

    fn add_gate_setup_polys_into_list<G: Gate<E>>(&mut self, gate: &G) {
        for key in gate.setup_polynomials().into_iter() {
            self.sorted_setup_polynomial_ids.push(key);
        }
    }

    fn add_gate_into_list<G: Gate<E>>(&mut self, gate: &G) {
        if !self.gates.contains(gate.as_internal() as &dyn GateInternal<E>) {
            self.gates.insert(gate.clone().into_internal());

            self.add_gate_setup_polys_into_list(gate);

            self.sorted_gates.push(gate.clone().into_internal());

            let degree = gate.degree();
            if self.max_constraint_degree < degree {
                self.max_constraint_degree = degree;
            }

            // let gate_constants = G::output_constant_coefficients::<E>();
            // self.sorted_gate_constants.push(gate_constants.clone());
            // self.gate_internal_coefficients.0.insert(Box::from(gate.clone().into_internal()), gate_constants);
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
            // gate_internal_coefficients: GateConstantCoefficientsStorage::<E>::new(),

            aux_gate_density: GateDensityStorage::new(),
            sorted_setup_polynomial_ids: vec![],
            sorted_gates: vec![],
            // sorted_gate_constants: vec![],

            is_finalized: false,

            explicit_zero_variable: None,
            explicit_one_variable: None,

            tables: vec![],
            multitables: vec![],
            table_selectors: std::collections::HashMap::new(),
            multitable_selectors: std::collections::HashMap::new(),
            table_ids_poly: vec![],

            individual_table_entries: std::collections::HashMap::new(),
            individual_multitable_entries: std::collections::HashMap::new(),

            known_table_ids: vec![],

            _marker: std::marker::PhantomData
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

        if (self.n()+1).is_power_of_two() {
            self.is_finalized = true;
            return;
        }

        let dummmy = Self::get_dummy_variable();

        let empty_gate = MainGateTerm::<E>::new();
        let (vars, coeffs) = MG::format_term(empty_gate, dummmy).expect("must make empty padding gate");

        let mg = MG::default();

        for _ in self.n()..(self.n().next_power_of_two() - 1) {
            self.new_single_gate_for_trace_step(
                &mg, 
                &coeffs, 
                &vars,
                &[]
            ).expect("must add padding gate");
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
        // expect a small number of inputs

        // TODO: handle public inputs

        // for i in 0..self.num_input_gates {
        //     let gate = self.input_assingments
        // }

        let one = E::Fr::one();
        let mut minus_one = E::Fr::one();
        minus_one.negate();

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

    pub(crate) fn make_permutations(&self, worker: &Worker) -> Vec<Polynomial::<E::Fr, Values>> {
        assert!(self.is_finalized);

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
            &domain, &worker
        );

        // domain_elements.pop().unwrap();

        use crate::ff::SqrtField;
        use crate::ff::LegendreSymbol;

        let mut non_residues = vec![];
        non_residues.push(E::Fr::one());
        non_residues.extend(make_non_residues::<E::Fr>(P::STATE_WIDTH - 1, &domain));

        assert_eq!(non_residues.len(), 4);

        let mut sigmas = vec![];
        for i in 0..P::STATE_WIDTH {
            let mut sigma_i = Polynomial::from_values_unpadded(domain_elements.clone()).unwrap();
            sigma_i.scale(&worker, non_residues[i]);
            sigmas.push(sigma_i);
        }

        let mut permutations = vec![vec![]; num_partitions + 1];

        fn rotate<T: Sized>(mut vec: Vec<T>) -> Vec<T> {
            if vec.len() > 1 {
                let mut els: Vec<_> = vec.drain(0..1).collect();
                els.reverse();
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

            // let permutation = partition.clone();
            // permutations[i] = permutation;

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

        sigmas
    }

    fn make_setup_polynomials(
        &self,
        with_finalization: bool
    ) -> Result<std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Values>>, SynthesisError> {
        if with_finalization {
            assert!(self.is_finalized);
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
                let aux_gates_coeffs = &mut assembled_poly[num_input_gates..];
                aux_gates_coeffs.copy_from_slice(&self.aux_storage.setup_map.get(&id).unwrap()[..]);
            }

            let as_poly = Polynomial::from_values_unpadded(assembled_poly)?;

            map.insert(id, as_poly);
        }

        Ok(map)
    }

    pub fn perform_setup(
        &self, 
        worker: &Worker
    ) -> Result<
    (std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Values>>, Vec<Polynomial<E::Fr, Values>>), 
    SynthesisError
    > {
        let map = self.make_setup_polynomials(true)?;
        let permutation_polys = self.make_permutations(&worker);

        Ok((map, permutation_polys))
    }

    pub fn output_gate_selectors(&self, worker: &Worker) -> Result<Vec<Polynomial<E::Fr, Values>>, SynthesisError> {
        assert!(self.is_finalized);
        if self.sorted_gates.len() == 1 {
            return Ok(vec![]);
        }

        let num_gate_selectors = self.sorted_gates.len();

        let one = E::Fr::one();
        let empty_poly = Polynomial::<E::Fr, Values>::new_for_size(self.n().next_power_of_two())?;
        let mut poly_values = vec![empty_poly.clone(); num_gate_selectors];
        let num_input_gates = self.num_input_gates;

        for p in poly_values.iter_mut() {
            for p in p.as_mut()[..num_input_gates].iter_mut() {
                *p = one;
            }
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
                        let poly_mut_slice: &mut [E::Fr] = &mut lh.as_mut()[num_input_gates..];
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

    pub fn make_state_and_witness_polynomials(
        &self,
        worker: &Worker,
        with_finalization: bool
    ) -> Result<(Vec<Vec<E::Fr>>, Vec<Vec<E::Fr>>), SynthesisError>
    {
        if with_finalization {
            assert!(self.is_finalized);
        }

        let mut full_assignments = if with_finalization {
            vec![Vec::with_capacity((self.n()+1).next_power_of_two()); P::STATE_WIDTH]
        } else {
            vec![Vec::with_capacity(self.n()+1); P::STATE_WIDTH]
        };

        let num_input_gates = self.num_input_gates;
        let num_aux_gates = self.num_aux_gates;

        full_assignments[0].extend_from_slice(&self.input_assingments);
        assert!(full_assignments[0].len() == num_input_gates);
        for i in 1..P::STATE_WIDTH {
            full_assignments[i].resize(num_input_gates, E::Fr::zero());
        }

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
                            let var = poly_ref[i];
                            let value = self.get_value(var).unwrap();
                            lh.push(value);
                        }
                    }
                });
            }
        });

        if with_finalization {
            for p in full_assignments.iter_mut() {
                p.resize((self.n()+1).next_power_of_two() - 1, E::Fr::zero());
            }

            for a in full_assignments.iter() {
                assert_eq!(a.len(), (self.n()+1).next_power_of_two() - 1);
            }
        }

        Ok((full_assignments, vec![]))
    }

    pub fn make_assembled_poly_storage(&self, worker: &Worker, with_finalization: bool) -> Result<AssembledPolynomialStorage<E>, SynthesisError> {
        if with_finalization {
            assert!(self.is_finalized);
        }
        
        let (state_polys, witness_polys) = self.make_state_and_witness_polynomials(&worker, with_finalization)?;
        let setup_polys_map = self.make_setup_polynomials(with_finalization)?;

        let mut state_polys_map = std::collections::HashMap::new();
        for (idx, poly) in state_polys.into_iter().enumerate() {
            let key = PolyIdentifier::VariablesPolynomial(idx);
            let p = Polynomial::from_values(poly)?;
            state_polys_map.insert(key, p);
        }

        let mut witness_polys_map = std::collections::HashMap::new();
        for (idx, poly) in witness_polys.into_iter().enumerate() {
            let key = PolyIdentifier::WitnessPolynomial(idx);
            let p = Polynomial::from_values(poly)?;
            witness_polys_map.insert(key, p);
        }

        let assembled = AssembledPolynomialStorage::<E> {
            state_map: state_polys_map,
            witness_map: witness_polys_map,
            setup_map: setup_polys_map,
            is_bitreversed: false,
            lde_factor: 1
        };

        Ok(assembled)
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

            let gamma = cs.alloc_input(|| {
                Ok(E::Fr::from_str("20").unwrap())
            })?;

            // gamma - b == 0 

            let gamma_term = ArithmeticTerm::from_variable(gamma);
            let b_term = ArithmeticTerm::from_variable(b);
            let mut term = MainGateTerm::new();
            term.add_assign(gamma_term);
            term.sub_assign(b_term);

            cs.allocate_main_gate(term)?;

            // 2a
            let mut term = MainGateTerm::<E>::new();
            term.add_assign(ArithmeticTerm::from_variable_and_coeff(a, two));

            let dummy = CS::get_dummy_variable();

            // 2a - d_next = 0

            let (vars, mut coeffs) = CS::MainGate::format_term(term, dummy)?;
            *coeffs.last_mut().unwrap() = negative_one;

            // here d is equal = 2a, so we need to place b there
            // and compensate it with -b somewhere before

            cs.new_single_gate_for_trace_step(&CS::MainGate::default(), 
                &coeffs, 
                &vars, 
                &[]
            )?;

            let mut term = MainGateTerm::<E>::new();
            term.add_assign(ArithmeticTerm::from_variable(b));

            // b + 0 + 0 - b = 0
            let (mut vars, mut coeffs) = CS::MainGate::format_term(term, dummy)?;
            coeffs[3] = negative_one;
            vars[3] = b;

            cs.new_single_gate_for_trace_step(&CS::MainGate::default(), 
                &coeffs, 
                &vars, 
                &[]
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_trivial_circuit_with_gate_agnostic_cs() {
        use crate::pairing::bn256::{Bn256, Fr};
        use crate::worker::Worker;

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        let circuit = TestCircuit4::<Bn256> {
            _marker: PhantomData
        };

        circuit.synthesize(&mut assembly).expect("must work");

        assert!(assembly.gates.len() == 1);

        // println!("Assembly state polys = {:?}", assembly.storage.state_map);

        // println!("Assembly setup polys = {:?}", assembly.storage.setup_map);    

        println!("Assembly contains {} gates", assembly.n());
        assembly.finalize();
        assert!(assembly.is_satisfied());

        assembly.finalize();

        let worker = Worker::new();

        let (_storage, _permutation_polys) = assembly.perform_setup(&worker).unwrap();
    }
}