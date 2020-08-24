use crate::pairing::{
    Engine,
};

use crate::pairing::ff::{
    Field,
    PrimeField,
    PrimeFieldRepr,
    BitIterator
};

use crate::{
    SynthesisError,
};

use crate::plonk::better_better_cs::cs::{
    Variable, 
    ConstraintSystem,
    ArithmeticTerm,
    MainGateTerm
};

use super::assignment::{
    Assignment
};

use std::ops::{Add, Sub};

pub struct AllocatedNum<E: Engine> {
    value: Option<E::Fr>,
    variable: Variable
}

impl<E: Engine> Clone for AllocatedNum<E> {
    fn clone(&self) -> Self {
        AllocatedNum {
            value: self.value,
            variable: self.variable
        }
    }
}

impl<E: Engine> AllocatedNum<E> {
    pub fn get_variable(&self) -> Variable {
        self.variable
    }

    pub fn get_value(&self) -> Option<E::Fr> {
        self.value
    }
    
    pub fn alloc<CS, F>(
        cs: &mut CS,
        value: F,
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>,
            F: FnOnce() -> Result<E::Fr, SynthesisError>
    {
        let mut new_value = None;
        let var = cs.alloc(
            || {
                let tmp = value()?;

                new_value = Some(tmp);

                Ok(tmp)
            }
        )?;

        Ok(AllocatedNum {
            value: new_value,
            variable: var
        })
    }

    pub fn alloc_zero<CS>(
        cs: &mut CS,
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let new_value = Some(E::Fr::zero());
        let var = CS::get_dummy_variable();

        Ok(AllocatedNum {
            value: new_value,
            variable: var
        })
    }

    pub fn add<CS>(
        &self,
        cs: &mut CS,
        other: &Self
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let mut value = None;

        let addition_result = cs.alloc(|| {
            let mut tmp = *self.value.get()?;
            tmp.add_assign(other.value.get()?);

            value = Some(tmp);

            Ok(tmp)
        })?;

        let self_term = ArithmeticTerm::from_variable(self.variable);
        let other_term = ArithmeticTerm::from_variable(other.variable);
        let result_term = ArithmeticTerm::from_variable(addition_result);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.add_assign(other_term);
        term.sub_assign(result_term);

        cs.allocate_main_gate(term)?;

        Ok(AllocatedNum {
            value: value,
            variable: addition_result
        })
    }

    pub fn add_constant<CS>(
        &self,
        cs: &mut CS,
        constant: E::Fr
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let mut value = None;

        let addition_result = cs.alloc(|| {
            let mut tmp = *self.value.get()?;
            tmp.add_assign(&constant);

            value = Some(tmp);

            Ok(tmp)
        })?;

        let self_term = ArithmeticTerm::from_variable(self.variable);
        let other_term = ArithmeticTerm::constant(constant);
        let result_term = ArithmeticTerm::from_variable(addition_result);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.add_assign(other_term);
        term.sub_assign(result_term);

        cs.allocate_main_gate(term)?;

        Ok(AllocatedNum {
            value: value,
            variable: addition_result
        })
    }

    pub fn mul<CS>(
        &self,
        cs: &mut CS,
        other: &Self
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let mut value = None;

        let product = cs.alloc(|| {
            let mut tmp = *self.value.get()?;
            tmp.mul_assign(other.value.get()?);

            value = Some(tmp);

            Ok(tmp)
        })?;

        let self_term = ArithmeticTerm::from_variable(self.variable).mul_by_variable(other.variable);
        let result_term = ArithmeticTerm::from_variable(product);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.sub_assign(result_term);

        cs.allocate_main_gate(term)?;

        Ok(AllocatedNum {
            value: value,
            variable: product
        })
    }

    pub fn square<CS>(
        &self,
        cs: &mut CS,
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        self.mul(cs, &self)
    }

    // given vector of coefs: [c0, c1, c2],
    // vector of vars: [var0, var1, var2],
    // and supposed result var,
    // ccheck if var = c0 * var0 + c1 * var1 + c2 * var2
    pub fn ternary_lc_eq<CS>(
        cs: &mut CS,
        coefs: &[E::Fr; 3],
        vars: &[Self; 3],
        res_var: &Self,
    ) -> Result<(), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        // check if equality indeed holds
        match (vars[0].get_value(), vars[1].get_value(), vars[2].get_value(), res_var.get_value()) {
            (Some(val0), Some(val1), Some(val2), Some(res_val)) => {

                let mut running_sum = val0;
                running_sum.mul_assign(&coefs[0]);

                let mut tmp = val1;
                tmp.mul_assign(&coefs[1]);
                running_sum.add_assign(tmp);

                let mut tmp = val2;
                tmp.mul_assign(&coefs[2]);
                running_sum.add_assign(tmp);

                assert_eq!(running_sum, res_val)
            }
            (_, _ , _ , _) => {},
        };

        let first_term = ArithmeticTerm::from_variable(vars[0].get_variable());
        first_term.scale(&coefs[0]);
        let second_term = ArithmeticTerm::from_variable(vars[1].get_variable());
        second_term.scale(&coefs[0]);
        let third_term = ArithmeticTerm::from_variable(vars[2].get_variable());
        third_term.scale(&coefs[0]);
        let result_term = ArithmeticTerm::from_variable(res_var.get_variable());
        
        let mut term = MainGateTerm::new();
        term.add_assign(first_term);
        term.add_assign(second_term);
        term.add_assign(third_term);
        term.sub_assign(result_term);
        cs.allocate_main_gate(term)?;

        Ok(())

    }
}


pub enum Num<E: Engine> {
    Alocated(AllocatedNum<E>),
    Constant(E::Fr),
}