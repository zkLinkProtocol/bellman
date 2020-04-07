use crate::pairing::ff::{Field};
use crate::pairing::{Engine};

use crate::{SynthesisError};
use std::marker::PhantomData;

pub use crate::plonk::cs::variable::*;

pub trait Circuit<E: Engine, P: PlonkConstraintSystemParams<E>> {
    fn synthesize<CS: ConstraintSystem<E, P>>(&self, cs: &mut CS) -> Result<(), SynthesisError>;
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum PolynomialInConstraint {
    VariablesPolynomial(usize, TimeDilation),
    WitnessPolynomial(usize, TimeDilation),
    SetupPolynomial(usize, TimeDilation)
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum PolyIdentifier {
    VariablesPolynomial(usize),
    WitnessPolynomial(usize),
    SetupPolynomial(usize),
}
// pub struct VariablesPolynomial(pub usize);
// pub struct WitnessPolynomial(pub usize);
// pub struct SetupPolynomial(pub usize);

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct TimeDilation(pub usize);

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct PolynomialMultiplicativeTerm(pub Vec<PolynomialInConstraint>);

impl PolynomialMultiplicativeTerm {
    fn degree(&self) -> usize {
        self.0.len()
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct LinearCombinationOfTerms(pub Vec<PolynomialMultiplicativeTerm>);

impl LinearCombinationOfTerms {
    fn terms(&self) -> &[PolynomialMultiplicativeTerm] {
       &self.0[..]
    }
}

pub trait GateEquation: GateEquationInternal
    + Sized
    + Clone
    + std::hash::Hash
    + std::default::Default 
{
    fn as_internal(&self) -> &dyn GateEquationInternal {
        self as &dyn GateEquationInternal
    }

    fn into_internal(self) -> Box<dyn GateEquationInternal> {
        Box::from(self) as Box<dyn GateEquationInternal>
    }
}

pub trait GateEquationInternal: Send 
    + Sync 
    + 'static 
    + std::any::Any 
{
    fn degree(&self) -> usize;
    fn num_constraints(&self) -> usize;
    fn get_constraint(&self) -> &LinearCombinationOfTerms;
    fn get_constraints(&self) -> &[LinearCombinationOfTerms];
}

// impl PartialEq for &[Term] {
//     fn eq(&self, other: &Self) -> bool {
//         if self.len() != other.len() {
//             return false;
//         }
//         for (l, r) in self.iter().zip(other.iter()) {
//             if l.0 != r.0 {
//                 return false;
//             }
//         }

//         true
//     }
// }

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

impl GateEquation for Width4MainGateWithDNextEquation {}

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
                    vec![
                        PolynomialInConstraint::VariablesPolynomial(i, TimeDilation(0)), 
                        PolynomialInConstraint::SetupPolynomial(i, TimeDilation(0))
                    ]
                )
            );
        }

        // multiplication
        terms.push(
            PolynomialMultiplicativeTerm(
                vec![
                    PolynomialInConstraint::VariablesPolynomial(0, TimeDilation(0)), 
                    PolynomialInConstraint::VariablesPolynomial(1, TimeDilation(0)), 
                    PolynomialInConstraint::SetupPolynomial(4, TimeDilation(0))
                ]
            )
        );

        // constant
        terms.push(
            PolynomialMultiplicativeTerm(
                vec![
                    PolynomialInConstraint::SetupPolynomial(5, TimeDilation(0))
                ]
            )
        );

        terms.push(
            PolynomialMultiplicativeTerm(
                vec![
                    PolynomialInConstraint::VariablesPolynomial(3, TimeDilation(1)), 
                    PolynomialInConstraint::SetupPolynomial(6, TimeDilation(0))
                ]
            )
        );

        Self([LinearCombinationOfTerms(terms)])
    }
}

fn check_gate_to_support_public_inputs<G: GateEquation>(gate: &G) -> bool {
    for t in gate.get_constraints() {
        for c in t.0.iter() {
            if c.0.len() != 1 {
                continue;
            }
            for s in c.0.iter() {
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
            for s in c.0.iter() {
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
                    PolynomialInConstraint::SetupPolynomial(_, TimeDilation(shift)) => {
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
            for s in c.0.iter() {
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
            for s in c.0.iter() {
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

fn max_addressed_setup_poly<G: GateEquation>(gate: &G) -> Option<usize> {
    let mut max: Option<usize> = None;

    for t in gate.get_constraints() {
        for c in t.0.iter() {
            for s in c.0.iter() {
                match s {
                    PolynomialInConstraint::SetupPolynomial(idx, _) => {
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

pub trait ConstraintSystem<E: Engine, P: PlonkConstraintSystemParams<E>> {
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

    fn get_dummy_variable(&self) -> Variable;
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
    pub state_map: std::collections::HashMap<PolyIdentifier, Vec<E::Fr>>,
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
}

struct TrivialAssembly<E: Engine, P: PlonkConstraintSystemParams<E>, MG: GateEquation> {
    storage: PolynomialStorage<E>,
    n: usize,
    max_constraint_degree: usize,
    main_gate: MG,
    input_assingments: Vec<E::Fr>,
    aux_assingments: Vec<E::Fr>,
    num_inputs: usize,
    num_aux: usize,
    trace_step_for_batch: Option<usize>,
    constraints: std::collections::HashSet<Box<dyn GateEquationInternal>>,
    _marker: std::marker::PhantomData<P>
}

impl<E: Engine, P: PlonkConstraintSystemParams<E>, MG: GateEquation> ConstraintSystem<E, P> for TrivialAssembly<E, P, MG> {
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

        self.n += 1;

        Ok(input_var)
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
        debug_assert!(check_gate_is_allowed_for_params::<E, P, G>(&gate));

        let mut coeffs_it = coefficients_assignments.iter();

        let mut setup_index: Option<usize> = None;

        for t in gate.get_constraints() {
            for c in t.0.iter() {
                for s in c.0.iter() {
                    match s {
                        PolynomialInConstraint::SetupPolynomial(idx, _) => {
                            setup_index = Some(*idx);
                        },
                        _ => {}
                    }

                    match setup_index.take() {
                        Some(idx) => {
                            let key = PolyIdentifier::SetupPolynomial(idx);
                            let poly_ref = self.storage.setup_map.entry(key).or_insert(vec![]);
                            poly_ref.push(*coeffs_it.next().expect("must get some coefficient for assignment"));
                        },
                        _ => {}
                    }
                }
            }
        }

        debug_assert!(coeffs_it.next().is_none(), "must consume all the coefficients for gate");

        if !self.constraints.contains(gate.as_internal() as &dyn GateEquationInternal) {
            self.constraints.insert(gate.clone().into_internal());
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

    fn get_dummy_variable(&self) -> Variable {
        self.dummy_variable()
    }
}

impl<E: Engine, P: PlonkConstraintSystemParams<E>, MG: GateEquation> TrivialAssembly<E, P, MG> {
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

            _marker: std::marker::PhantomData
        };

        tmp.max_constraint_degree = tmp.main_gate.degree();

        assert!(check_gate_to_support_public_inputs(&tmp.main_gate), "default gate must support making public inputs");

        tmp
    }

    // return variable that is not in a constraint formally, but has some value
    fn dummy_variable(&self) -> Variable {
        Variable(Index::Aux(0))
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

    impl<E: Engine> Circuit<E, PlonkCsWidth4WithNextStepParams> for TestCircuit4<E> {
        fn synthesize<CS: ConstraintSystem<E, PlonkCsWidth4WithNextStepParams> >(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let main_gate = Width4MainGateWithDNextEquation::default();

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

            let zero = E::Fr::zero();

            let one = E::Fr::one();

            let mut two = one;
            two.double();

            let mut negative_one = one;
            negative_one.negate();

            let dummy = cs.get_dummy_variable();

            cs.new_single_gate_for_trace_step(
                &main_gate, 
                &[two, negative_one, zero, zero, zero, zero, zero],
                &[a, b, dummy, dummy], 
                &[]
            )?;

            // 10b - c = 0
            let ten = E::Fr::from_str("10").unwrap();

            cs.new_single_gate_for_trace_step(
                &main_gate, 
                &[ten, negative_one, zero, zero, zero, zero, zero],
                &[b, c, dummy, dummy], 
                &[]
            )?;

            // c - a*b == 0 

            cs.new_single_gate_for_trace_step(
                &main_gate, 
                &[zero, zero, zero, negative_one, one, zero, zero],
                &[a, b, dummy, c], 
                &[]
            )?;

            // 10a + 10b - c - d == 0

            cs.new_single_gate_for_trace_step(
                &main_gate, 
                &[ten, ten, negative_one, negative_one, zero, zero, zero],
                &[a, b, c, d], 
                &[]
            )?;

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
    }
}