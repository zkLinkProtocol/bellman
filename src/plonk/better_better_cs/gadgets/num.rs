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
        _cs: &mut CS,
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
    // check if var = c0 * var0 + c1 * var1 + c2 * var2
    pub fn ternary_lc_eq<CS>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
        res_var: &Self,
    ) -> Result<(), SynthesisError>
        where CS: ConstraintSystem<E>
    {
        assert_eq!(coefs.len(), vars.len());
        assert_eq!(coefs.len(), 3);
        
        // check if equality indeed holds
        match (vars[0].get_value(), vars[1].get_value(), vars[2].get_value(), res_var.get_value()) {
            (Some(val0), Some(val1), Some(val2), Some(res_val)) => {

                let mut running_sum = val0;
                running_sum.mul_assign(&coefs[0]);

                let mut tmp = val1;
                tmp.mul_assign(&coefs[1]);
                running_sum.add_assign(&tmp);

                let mut tmp = val2;
                tmp.mul_assign(&coefs[2]);
                running_sum.add_assign(&tmp);

                assert_eq!(running_sum, res_val)
            }
            (_, _ , _ , _) => {},
        };

        let mut first_term = ArithmeticTerm::from_variable(vars[0].get_variable());
        first_term.scale(&coefs[0]);
        let mut second_term = ArithmeticTerm::from_variable(vars[1].get_variable());
        second_term.scale(&coefs[0]);
        let mut third_term = ArithmeticTerm::from_variable(vars[2].get_variable());
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

    // given vector of coefs: [c0, c1, c2],
    // vector of vars: [var0, var1, var2],
    // and constant_elem : c
    // constrcuts if var = c0 * var0 + c1 * var1 + c2 * var2 + c
    pub fn ternary_lc_with_const<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
        c: &E::Fr,
    ) -> Result<Self, SynthesisError>
    {
        assert_eq!(coefs.len(), vars.len());
        assert_eq!(coefs.len(), 3);
        
        let new_val = match (vars[0].get_value(), vars[1].get_value(), vars[2].get_value()) {
            (Some(val0), Some(val1), Some(val2)) => {

                let mut running_sum = val0;
                running_sum.mul_assign(&coefs[0]);

                let mut tmp = val1;
                tmp.mul_assign(&coefs[1]);
                running_sum.add_assign(&tmp);

                let mut tmp = val2;
                tmp.mul_assign(&coefs[2]);
                running_sum.add_assign(&tmp);

                running_sum.add_assign(&c);
                Some(running_sum)
            },
            (_, _ , _ ) => None,
        };

        let res_var = AllocatedNum::alloc(cs, || new_val.grab())?;

        let mut first_term = ArithmeticTerm::from_variable(vars[0].get_variable());
        first_term.scale(&coefs[0]);
        let mut second_term = ArithmeticTerm::from_variable(vars[1].get_variable());
        second_term.scale(&coefs[0]);
        let mut third_term = ArithmeticTerm::from_variable(vars[2].get_variable());
        third_term.scale(&coefs[0]);
        let result_term = ArithmeticTerm::from_variable(res_var.get_variable());
        let const_term = ArithmeticTerm::constant(c.clone());
        
        let mut term = MainGateTerm::new();
        term.add_assign(first_term);
        term.add_assign(second_term);
        term.add_assign(third_term);
        term.sub_assign(result_term);
        term.add_assign(const_term);
        cs.allocate_main_gate(term)?;

        Ok(res_var)
    }

    // for given array of slices : [x0, x1, x2, ..., xn] of arbitrary length, base n and total accumulated x
    // validates that x = x0 + x1 * base + x2 * base^2 + ... + xn * base^n
    pub fn long_weighted_sum_eq<CS>(cs: &mut CS, vars: &[Self], base: &E::Fr, total: &Self) -> Result<(), SynthesisError>
    where CS: ConstraintSystem<E>
    {
        let mut acc_fr = E::Fr::one();
        let mut coeffs = Vec::with_capacity(4);
        let mut current_vars = Vec::with_capacity(4);

        for var in vars.iter() {
            if vars.len() < 3 {
                coeffs.push(acc_fr.clone());
                acc_fr.mul_assign(&base);
                current_vars.push(var.clone());
            }
            else {
                // we have filled in the whole vector!
                let temp = AllocatedNum::ternary_lc_with_const(cs, &coeffs[..], &current_vars[..], &E::Fr::zero())?;
                coeffs = vec![E::Fr::one()];
                current_vars = vec![temp];
            }
        }

        // pad with dummy variables
        for _i in vars.len()..3 {
            current_vars.push(AllocatedNum::alloc_zero(cs)?);
            coeffs.push(E::Fr::zero());
        }

        AllocatedNum::ternary_lc_eq(cs, &coeffs[..], &vars[..], total)?;
        Ok(())
    }
}


#[derive(Clone)]
pub enum Num<E: Engine> {
    Allocated(AllocatedNum<E>),
    Constant(E::Fr),
}


impl<E: Engine> Num<E> {
    pub fn is_constant(&self) -> bool 
    {
        match self {
            Num::Allocated(_) => false,
            Num::Constant(_) => true,
        }
    }

    pub fn get_value(&self) -> Option<E::Fr>
    {
        match self {
            Num::Constant(x) => Some(x.clone()),
            Num::Allocated(x) => x.get_value(),
        }
    }

    // pub fn add<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError>
    // {
    //     mat
    // }

    // pub fn add_two


    pub fn lc<CS: ConstraintSystem<E>>(cs: &mut CS, coeffs: &[E::Fr], nums: &[Num<E>]) -> Result<Self, SynthesisError>
    {
        assert_eq!(coeffs.len(), nums.len());

        // corner case: all our values are actually constants
        if nums.iter().all(| x | x.is_constant()) {
            let value = nums.iter().zip(coeffs.iter()).fold(E::Fr::zero(), |acc, (x, coef)| {
                let mut temp = x.get_value().unwrap();
                temp.mul_assign(&coef);
                temp.add_assign(&acc);
                temp
            });

            return Ok(Num::Constant(value));
        }

        // okay, from now one we may be sure that we have at least one allocated term
        let mut constant_term = E::Fr::zero();
        let mut vars = Vec::with_capacity(3);
        let mut local_coeffs = Vec::with_capacity(3);
        let mut first_lc = true;
        let mut res_var = AllocatedNum::alloc_zero(cs)?;

        // Note: the whole thing may be a little more efficient with the use of custom gates
        // exploiting (d_next)

        for (x, coef) in nums.iter().zip(coeffs.iter()) {
            match x {
                Num::Constant(x) => {
                    let mut temp = x.clone();
                    temp.mul_assign(&coef);
                    constant_term.add_assign(&temp);
                },
                Num::Allocated(x) => {
                    if vars.is_empty() && !first_lc {
                        vars.push(res_var.clone());
                        local_coeffs.push(E::Fr::one());
                    }
                    else if vars.len() < 3 
                    {
                        vars.push(x.clone());
                        local_coeffs.push(coef.clone());
                    }
                    else {
                        // we already have three elements in our vector
                        first_lc = false;
                        res_var = AllocatedNum::ternary_lc_with_const(cs, &local_coeffs[..], &vars[..], &constant_term)?;

                        constant_term = E::Fr::zero();
                        vars = Vec::with_capacity(3);
                        local_coeffs = Vec::with_capacity(3);
                    }
                }
            }
        }

        if !vars.is_empty() {
            // pad with dummy variables
            for _i in vars.len()..3 {
                vars.push(AllocatedNum::alloc_zero(cs)?);
                local_coeffs.push(E::Fr::zero());
            }
            res_var = AllocatedNum::ternary_lc_with_const(cs, &coeffs[..], &vars[..], &constant_term)?;
        }

        Ok(Num::Allocated(res_var))
    }
}