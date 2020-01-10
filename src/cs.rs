use crate::pairing::{Engine};
use crate::pairing::ff::Field;

use std::ops::{Add, Sub};
use std::fmt;
use std::error::Error;
use std::io;
use std::marker::PhantomData;

extern crate tokio;

use tokio::runtime::Runtime;

/// Computations are expressed in terms of arithmetic circuits, in particular
/// rank-1 quadratic constraint systems. The `Circuit` trait represents a
/// circuit that can be synthesized. The `synthesize` method is called during
/// CRS generation and during proving.
pub trait Circuit<E: Engine> {
    /// Synthesize the circuit into a rank-1 quadratic constraint system
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>;
}

/// Represents a variable in our constraint system.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct Variable(pub(crate) Index);

impl Variable {
    /// This constructs a variable with an arbitrary index.
    /// Circuit implementations are not recommended to use this.
    pub fn new_unchecked(idx: Index) -> Variable {
        Variable(idx)
    }

    /// This returns the index underlying the variable.
    /// Circuit implementations are not recommended to use this.
    pub fn get_unchecked(&self) -> Index {
        self.0
    }
}

/// Represents the index of either an input variable or
/// auxillary variable.
#[derive(Copy, Clone, PartialEq, Debug, Hash, Eq)]
pub enum Index {
    Input(usize),
    Aux(usize)
}

/// This represents a linear combination of some variables, with coefficients
/// in the scalar field of a pairing-friendly elliptic curve group.
#[derive(Clone, Debug, Eq)]
pub struct LinearCombination<E: Engine>(pub(crate) Vec<(Variable, E::Fr)>);

impl<E: Engine> PartialEq for LinearCombination<E> {
    fn eq(&self, other: &LinearCombination<E>) -> bool {
        self.0==other.0
    }
}

impl<E: Engine> AsRef<[(Variable, E::Fr)]> for LinearCombination<E> {
    fn as_ref(&self) -> &[(Variable, E::Fr)] {
        &self.0
    }
}

impl<E: Engine> LinearCombination<E> {
    pub fn zero() -> LinearCombination<E> {
        LinearCombination(vec![])
    }
}

impl<E: Engine> Add<(E::Fr, Variable)> for LinearCombination<E> {
    type Output = LinearCombination<E>;

    fn add(mut self, (coeff, var): (E::Fr, Variable)) -> LinearCombination<E> {
        self.0.push((var, coeff));

        self
    }
}

impl<E: Engine> Sub<(E::Fr, Variable)> for LinearCombination<E> {
    type Output = LinearCombination<E>;

    fn sub(self, (mut coeff, var): (E::Fr, Variable)) -> LinearCombination<E> {
        coeff.negate();

        self + (coeff, var)
    }
}

impl<E: Engine> Add<Variable> for LinearCombination<E> {
    type Output = LinearCombination<E>;

    fn add(self, other: Variable) -> LinearCombination<E> {
        self + (E::Fr::one(), other)
    }
}

impl<E: Engine> Sub<Variable> for LinearCombination<E> {
    type Output = LinearCombination<E>;

    fn sub(self, other: Variable) -> LinearCombination<E> {
        self - (E::Fr::one(), other)
    }
}

impl<'a, E: Engine> Add<&'a LinearCombination<E>> for LinearCombination<E> {
    type Output = LinearCombination<E>;

    fn add(mut self, other: &'a LinearCombination<E>) -> LinearCombination<E> {
        for s in &other.0 {
            self = self + (s.1, s.0);
        }

        self
    }
}

impl<'a, E: Engine> Sub<&'a LinearCombination<E>> for LinearCombination<E> {
    type Output = LinearCombination<E>;

    fn sub(mut self, other: &'a LinearCombination<E>) -> LinearCombination<E> {
        for s in &other.0 {
            self = self - (s.1, s.0);
        }

        self
    }
}

impl<'a, E: Engine> Add<(E::Fr, &'a LinearCombination<E>)> for LinearCombination<E> {
    type Output = LinearCombination<E>;

    fn add(mut self, (coeff, other): (E::Fr, &'a LinearCombination<E>)) -> LinearCombination<E> {
        for s in &other.0 {
            let mut tmp = s.1;
            tmp.mul_assign(&coeff);
            self = self + (tmp, s.0);
        }

        self
    }
}

impl<'a, E: Engine> Sub<(E::Fr, &'a LinearCombination<E>)> for LinearCombination<E> {
    type Output = LinearCombination<E>;

    fn sub(mut self, (coeff, other): (E::Fr, &'a LinearCombination<E>)) -> LinearCombination<E> {
        for s in &other.0 {
            let mut tmp = s.1;
            tmp.mul_assign(&coeff);
            self = self - (tmp, s.0);
        }

        self
    }
}

/// This is an error that could occur during circuit synthesis contexts,
/// such as CRS generation, proving or verification.
#[derive(Debug)]
pub enum SynthesisError {
    /// During synthesis, we lacked knowledge of a variable assignment.
    AssignmentMissing,
    /// During synthesis, we divided by zero.
    DivisionByZero,
    /// During synthesis, we constructed an unsatisfiable constraint system.
    Unsatisfiable,
    /// During synthesis, our polynomials ended up being too high of degree
    PolynomialDegreeTooLarge,
    /// During proof generation, we encountered an identity in the CRS
    UnexpectedIdentity,
    /// During proof generation, we encountered an I/O error with the CRS
    IoError(io::Error),
    /// During verification, our verifying key was malformed.
    MalformedVerifyingKey,
    /// During CRS generation, we observed an unconstrained auxillary variable
    UnconstrainedVariable
}

impl From<io::Error> for SynthesisError {
    fn from(e: io::Error) -> SynthesisError {
        SynthesisError::IoError(e)
    }
}

impl Error for SynthesisError {
    fn description(&self) -> &str {
        match *self {
            SynthesisError::AssignmentMissing => "an assignment for a variable could not be computed",
            SynthesisError::DivisionByZero => "division by zero",
            SynthesisError::Unsatisfiable => "unsatisfiable constraint system",
            SynthesisError::PolynomialDegreeTooLarge => "polynomial degree is too large",
            SynthesisError::UnexpectedIdentity => "encountered an identity element in the CRS",
            SynthesisError::IoError(_) => "encountered an I/O error",
            SynthesisError::MalformedVerifyingKey => "malformed verifying key",
            SynthesisError::UnconstrainedVariable => "auxillary variable was unconstrained"
        }
    }
}

impl fmt::Display for SynthesisError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if let &SynthesisError::IoError(ref e) = self {
            write!(f, "I/O error: ")?;
            e.fmt(f)
        } else {
            write!(f, "{}", self.description())
        }
    }
}

use std::sync::mpsc::Sender;
use std::sync::mpsc::Receiver;

/// Represents a constraint system which can have new variables
/// allocated and constrains between them formed.
pub trait ConstraintSystem<E: Engine>: Sized {
    /// Represents the type of the "root" of this constraint system
    /// so that nested namespaces can minimize indirection.
    type Root: ConstraintSystem<E>;

    /// Return the "one" input variable
    fn one() -> Variable {
        Variable::new_unchecked(Index::Input(0))
    }

    /// Allocate a private variable in the constraint system. The provided function is used to
    /// determine the assignment of the variable. The given `annotation` function is invoked
    /// in testing contexts in order to derive a unique name for this variable in the current
    /// namespace.
    fn alloc<F, A, AR>(
        &mut self,
        annotation: A,
        f: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>;

    /// Allocate a public variable in the constraint system. The provided function is used to
    /// determine the assignment of the variable.
    fn alloc_input<F, A, AR>(
        &mut self,
        annotation: A,
        f: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>;

    /// Enforce that `A` * `B` = `C`. The `annotation` function is invoked in testing contexts
    /// in order to derive a unique name for the constraint in the current namespace.
    fn enforce<A, AR, LA, LB, LC>(
        &mut self,
        annotation: A,
        a: LA,
        b: LB,
        c: LC
    )
        where A: FnOnce() -> AR, AR: Into<String>,
              LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
              LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
              LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>;

    /// Create a new (sub)namespace and enter into it. Not intended
    /// for downstream use; use `namespace` instead.
    fn push_namespace<NR, N>(&mut self, name_fn: N)
        where NR: Into<String>, N: FnOnce() -> NR;

    /// Exit out of the existing namespace. Not intended for
    /// downstream use; use `namespace` instead.
    fn pop_namespace(&mut self);

    /// Gets the "root" constraint system, bypassing the namespacing.
    /// Not intended for downstream use; use `namespace` instead.
    fn get_root(&mut self) -> &mut Self::Root;

    /// Begin a namespace for this constraint system.
    fn namespace<'a, NR, N>(
        &'a mut self,
        name_fn: N
    ) -> Namespace<'a, E, Self::Root>
        where NR: Into<String>, N: FnOnce() -> NR
    {
        self.get_root().push_namespace(name_fn);

        Namespace(self.get_root(), PhantomData)
    }

    /// Add new ThreadConstraintSystem.
    fn reserve_memory_for_thread_info(
        &mut self
    ) -> Sender<RememberedInfo<E>>
    {
        panic!("only for reimplemented calling");
    }

    fn alloc_thread_output<F, A, AR>(
        &mut self,
        annotation: A,
        f: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        panic!("only for reimplemented calling");
    }
}

use std::collections::HashMap;

#[derive(Clone)]
pub struct RememberedInfo<E: Engine>
{
    pub last_used_index: usize,
    pub constraints: Vec<(String, LinearCombination<E>, LinearCombination<E>, LinearCombination<E>)>,
    pub outside_variables: HashMap<Variable,Variable>, /// (in thread, global cs)
    pub thread_outputs: HashMap<Variable,Variable>, /// (in thread, global cs)
    pub my_aux_values: Vec<E::Fr>,
}

// TODO :: description
pub struct ThreadConstraintSystem<E: Engine, CS: ConstraintSystem<E>>
(
    RememberedInfo<E>,
    PhantomData<CS>,
);

impl<E: Engine, CS: ConstraintSystem<E>> ThreadConstraintSystem<E, CS>
{
    pub fn new() -> Self
    {
        ThreadConstraintSystem(
            RememberedInfo {
                last_used_index: 0,
                constraints: vec![],
                outside_variables: HashMap::new(),
                thread_outputs: HashMap::new(),
                my_aux_values: vec![],
            },
            PhantomData
        )
    }

    pub fn get_rem_info(
        &mut self
    ) -> RememberedInfo<E>
    {
        self.0.clone()
    }

    pub fn add_outside_variable(&mut self, var1: Variable, var2: Variable)
    {
        self.0.outside_variables.insert(var1,var2);
    }

    pub fn add_thread_output(&mut self, var1: Variable, var2: Variable) { self.0.thread_outputs.insert(var1,var2); }

    pub fn get_constraints(
        &mut self
    ) -> Vec<(String, LinearCombination<E>, LinearCombination<E>, LinearCombination<E>)>
    {
//        self.runtime.shutdown_on_idle().wait().unwrap();

        self.0.constraints.clone()
    }
}

impl<E: Engine, CS: ConstraintSystem<E>> ConstraintSystem<E> for ThreadConstraintSystem<E, CS> {
    type Root = Self;

    fn one() -> Variable { CS::one() }

    fn alloc<F, A, AR>(
        &mut self,
        annotation: A,
        f: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        self.0.my_aux_values.push(f()?);
        self.0.last_used_index += 1;
        Ok(Variable(Index::Aux(self.0.last_used_index - 1)))
    }

    fn alloc_input<F, A, AR>(
        &mut self,
        annotation: A,
        f: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        panic!("not available in this context");
    }

    fn enforce<A, AR, LA, LB, LC>(
        &mut self,
        annotation: A,
        a: LA,
        b: LB,
        c: LC
    )
        where A: FnOnce() -> AR, AR: Into<String>,
              LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
              LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
              LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>
    {
        let a = a(LinearCombination::zero());
        let b = b(LinearCombination::zero());
        let c = c(LinearCombination::zero());
        self.0.constraints.push((annotation().into(),a,b,c));
    }

    // Downstream users who use `namespace` will never interact with these
    // functions and they will never be invoked because the namespace is
    // never a root constraint system.

    fn push_namespace<NR, N>(&mut self, _: N)
        where NR: Into<String>, N: FnOnce() -> NR
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self)
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn get_root(&mut self) -> &mut Self::Root { self }
}

/// This is a "namespaced" constraint system which borrows a constraint system (pushing
/// a namespace context) and, when dropped, pops out of the namespace context.
pub struct Namespace<'a, E: Engine, CS: ConstraintSystem<E> + 'a>(&'a mut CS, PhantomData<E>);

impl<'cs, E: Engine, CS: ConstraintSystem<E>> ConstraintSystem<E> for Namespace<'cs, E, CS> {
    type Root = CS::Root;

    fn one() -> Variable {
        CS::one()
    }

    fn alloc<F, A, AR>(
        &mut self,
        annotation: A,
        f: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        self.0.alloc(annotation, f)
    }

    fn alloc_input<F, A, AR>(
        &mut self,
        annotation: A,
        f: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        self.0.alloc_input(annotation, f)
    }

    fn enforce<A, AR, LA, LB, LC>(
        &mut self,
        annotation: A,
        a: LA,
        b: LB,
        c: LC
    )
        where A: FnOnce() -> AR, AR: Into<String>,
              LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
              LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
              LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>
    {
        self.0.enforce(annotation, a, b, c)
    }

    // Downstream users who use `namespace` will never interact with these
    // functions and they will never be invoked because the namespace is
    // never a root constraint system.

    fn push_namespace<NR, N>(&mut self, _: N)
        where NR: Into<String>, N: FnOnce() -> NR
    {
        panic!("only the root's push_namespace should be called");
    }

    fn pop_namespace(&mut self)
    {
        panic!("only the root's pop_namespace should be called");
    }

    fn get_root(&mut self) -> &mut Self::Root
    {
        self.0.get_root()
    }

    fn reserve_memory_for_thread_info(
        &mut self
    ) -> Sender<RememberedInfo<E>>
    {
        self.0.reserve_memory_for_thread_info()
    }

    fn alloc_thread_output<F, A, AR>(
        &mut self,
        annotation: A,
        f: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        self.0.alloc_thread_output(annotation, f)
    }
}

impl<'a, E: Engine, CS: ConstraintSystem<E>> Drop for Namespace<'a, E, CS> {
    fn drop(&mut self) {
        self.get_root().pop_namespace()
    }
}

/// Convenience implementation of ConstraintSystem<E> for mutable references to
/// constraint systems.
impl<'cs, E: Engine, CS: ConstraintSystem<E>> ConstraintSystem<E> for &'cs mut CS {
    type Root = CS::Root;

    fn one() -> Variable {
        CS::one()
    }

    fn alloc<F, A, AR>(
        &mut self,
        annotation: A,
        f: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        (**self).alloc(annotation, f)
    }

    fn alloc_input<F, A, AR>(
        &mut self,
        annotation: A,
        f: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        (**self).alloc_input(annotation, f)
    }

    fn enforce<A, AR, LA, LB, LC>(
        &mut self,
        annotation: A,
        a: LA,
        b: LB,
        c: LC
    )
        where A: FnOnce() -> AR, AR: Into<String>,
              LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
              LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
              LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>
    {
        (**self).enforce(annotation, a, b, c)
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
        where NR: Into<String>, N: FnOnce() -> NR
    {
        (**self).push_namespace(name_fn)
    }

    fn pop_namespace(&mut self)
    {
        (**self).pop_namespace()
    }

    fn get_root(&mut self) -> &mut Self::Root
    {
        (**self).get_root()
    }

    fn reserve_memory_for_thread_info(
        &mut self
    ) -> Sender<RememberedInfo<E>>
    {
        (**self).reserve_memory_for_thread_info()
    }

    fn alloc_thread_output<F, A, AR>(
        &mut self,
        annotation: A,
        f: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        (**self).alloc_thread_output(annotation, f)
    }
}