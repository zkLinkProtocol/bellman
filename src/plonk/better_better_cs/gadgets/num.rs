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
    Index,
    ConstraintSystem,
    ArithmeticTerm,
    MainGateTerm,
    MainGate
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

impl<E: Engine> Default for AllocatedNum<E> {
    fn default() -> Self {
        AllocatedNum  {
            value: None,
            variable: Variable(Index::Aux(0)),
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

    pub fn alloc_input<CS, F>(
        cs: &mut CS,
        value: F,
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>,
            F: FnOnce() -> Result<E::Fr, SynthesisError>
    {
        let mut new_value = None;
        let var = cs.alloc_input(
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

    // TODO: rename to alloc_dummy
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

    pub fn alloc_cnst<CS>(
        cs: &mut CS, fr: E::Fr,
    ) -> Result<Self, SynthesisError>
        where CS: ConstraintSystem<E>
    {
        let var = cs.alloc(|| { Ok(fr.clone()) })?;

        let self_term = ArithmeticTerm::<E>::from_variable(var);
        let other_term = ArithmeticTerm::constant(fr.clone());
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.sub_assign(other_term);

        cs.allocate_main_gate(term)?;

        Ok(AllocatedNum {
            value: Some(fr),
            variable: var
        })
    }

    pub fn alloc_from_lc<CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        coefs: &[E::Fr],
        vars: &[Self],
        cnst: &E::Fr
    ) -> Result<Self, SynthesisError>
    {
        assert_eq!(coefs.len(), vars.len());
        
        let new_value = match vars.iter().all(|x| x.get_value().is_some()) {
            false => None,
            true => {
                let mut res = cnst.clone();
                for (var, coef) in vars.iter().zip(coefs.iter()) {
                    let mut tmp = var.get_value().unwrap();
                    tmp.mul_assign(coef);
                    res.add_assign(&tmp);
                }
                Some(res)
            },
        };

        Self::alloc(cs, || new_value.grab())
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

    pub fn add_two<CS: ConstraintSystem<E>>(&self, cs: &mut CS, x: Self, y: Self) -> Result<Self, SynthesisError>
    {     
        let mut value = None;

        let addition_result = cs.alloc(|| {
            let mut tmp = *self.value.get()?;
            let tmp2 = x.value.get()?;
            let tmp3 = y.value.get()?;
            tmp.add_assign(&tmp2);
            tmp.add_assign(&tmp3);
            value = Some(tmp);
            Ok(tmp)
        })?;

        let self_term = ArithmeticTerm::from_variable(self.variable);
        let other_term = ArithmeticTerm::from_variable(x.variable);
        let third_term = ArithmeticTerm::from_variable(y.variable);
        let result_term = ArithmeticTerm::from_variable(addition_result);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.add_assign(other_term);
        term.add_assign(third_term);
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

    pub fn eq<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: Self) -> Result<(), SynthesisError>
    {
        let self_term = ArithmeticTerm::from_variable(self.variable);
        let other_term = ArithmeticTerm::from_variable(other.variable);
        let mut term = MainGateTerm::new();
        term.add_assign(self_term);
        term.sub_assign(other_term);

        cs.allocate_main_gate(term)?;

        Ok(())
    }

    // given vector of coefs: [c0, c1, c2, c3],
    // vector of vars: [var0, var1, var2, var3],
    // next row var and coef: c4 and var4
    // and additional constant: cnst
    // constrcut the gate asserting that: 
    // c0 * var0 + c1 * var1 + c2 * var3 + c4 * var4 + cnst = 0
    // here the state is [var0, var1, var2, var3]
    // and var4 should be placed on the next row with the help of d_next
    pub fn general_lc_gate<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
        cnst: &E::Fr,
        next_row_coef: &E::Fr,
        next_row_var: &Self,
    ) -> Result<(), SynthesisError>
    {
        assert_eq!(coefs.len(), vars.len());
        assert_eq!(coefs.len(), 4);
        
        // check if equality indeed holds
        // TODO: do it only in debug mde!
        match (vars[0].get_value(), vars[1].get_value(), vars[2].get_value(), vars[3].get_value(), next_row_var.get_value()) {
            (Some(val0), Some(val1), Some(val2), Some(val3), Some(val4)) => {
                let mut running_sum = val0;
                running_sum.mul_assign(&coefs[0]);

                let mut tmp = val1;
                tmp.mul_assign(&coefs[1]);
                running_sum.add_assign(&tmp);

                let mut tmp = val2;
                tmp.mul_assign(&coefs[2]);
                running_sum.add_assign(&tmp);

                let mut tmp = val3;
                tmp.mul_assign(&coefs[3]);
                running_sum.add_assign(&tmp);

                let mut tmp = val4;
                tmp.mul_assign(&next_row_coef);
                running_sum.add_assign(&tmp);

                running_sum.add_assign(&cnst);
                assert_eq!(running_sum, E::Fr::zero())
            }
            _ => {},
        };

        let dummy = Self::alloc_zero(cs)?;
        let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
        let mut gate_term = MainGateTerm::new();
        let (mut local_vars, mut local_coeffs) = CS::MainGate::format_term(gate_term, dummy.variable)?;
        for (i, idx) in range_of_linear_terms.enumerate() {
            local_coeffs[idx] = coefs[i].clone();
        }
  
        let cnst_index = CS::MainGate::index_for_constant_term();
        local_coeffs[cnst_index] = *cnst;

        let next_row_term_idx = CS::MainGate::range_of_next_step_linear_terms().last().unwrap();
        local_coeffs[next_row_term_idx] = next_row_coef.clone();

        let mg = CS::MainGate::default();
        local_vars = vec![vars[0].get_variable(), vars[1].get_variable(), vars[2].get_variable(), vars[3].get_variable()];

        cs.new_single_gate_for_trace_step(
            &mg,
            &local_coeffs,
            &local_vars,
            &[]
        )?;

        Ok(())
    }

    // given vector of coefs: [c0, c1, c2, c3],
    // vector of vars: [var0, var1, var2, var3, var4],
    // and additional constant: cnst
    // allocate new variable res equal to c0 * var0 + c1 * var1 + c2 * var2 + c3 * var3
    // assuming res is placed in d register of the next row
    pub fn quartic_lc_with_cnst<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
        cnst: &E::Fr,
    ) -> Result<Self, SynthesisError>
    {
        let res = AllocatedNum::alloc_from_lc(cs, coefs, vars, cnst)?;
        let mut minus_one = E::Fr::one();
        minus_one.negate();

        AllocatedNum::general_lc_gate(cs, coefs, vars, cnst, &minus_one, &res)?;
        Ok(res)
    }

    pub fn quartic_lc<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
    ) -> Result<Self, SynthesisError>
    {
        let res = AllocatedNum::alloc_from_lc(cs, coefs, vars, cnst)?;
        let mut minus_one = E::Fr::one();
        minus_one.negate();

        AllocatedNum::general_lc_gate(cs, coefs, vars, cnst, &minus_one, &res)?;
        Ok(res)
    }

    pub fn quartic_lc_eq<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
        total: &Self,
    ) -> Result<(), SynthesisError>
    {
        let mut minus_one = E::Fr::one();
        minus_one.negate();
        AllocatedNum::general_lc_gate(cs, coefs, vars, &E::Fr::zero(), &minus_one, &total)
    }

    pub fn ternary_lc_eq<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
        total: &Self,
    ) -> Result<(), SynthesisError>
    {
        assert_eq!(coefs.len(), vars.len());
        assert_eq!(coefs.len(), 3);

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let mut local_coefs = vec![];
        local_coefs.extend_from_slice(coefs);
        local_coefs.push(minus_one);
        
        let mut local_vars = vec![];
        local_vars.extend_from_slice(vars);
        local_vars.push(*total);

        AllocatedNum::general_lc_gate(
            cs, &local_coefs[..], &local_vars[..], &E::Fr::zero(), &E::Fr::zero(), &AllocatedNum::alloc_zero(cs)?
        )
    }

    pub fn ternary_lc_with_cnst<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        coefs: &[E::Fr],
        vars: &[Self],
        cnst: &E::Fr,
    ) -> Result<Self, SynthesisError>
    {
        assert_eq!(coefs.len(), vars.len());
        assert_eq!(coefs.len(), 3);

        let res = AllocatedNum::alloc_from_lc(cs, coefs, vars, cnst)?;
        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let mut local_coefs = vec![];
        local_coefs.extend_from_slice(coefs);
        local_coefs.push(minus_one);

        let mut local_vars = vec![];
        local_vars.extend_from_slice(vars);
        local_vars.push(res);

        AllocatedNum::general_lc_gate(
            cs, &local_coefs[..], &local_vars[..], &E::Fr::zero(), &E::Fr::zero(), &AllocatedNum::alloc_zero(cs)?
        )?;

        Ok(res)
    }

    // for given array of slices : [x0, x1, x2, ..., xn] of arbitrary length, base n and total accumulated x
    // validates that x = x0 + x1 * base + x2 * base^2 + ... + xn * base^n
    // use_d_next flag allows to place total on the next row, without expicitely constraiting it and leaving
    // is as a job for the next gate allocation.
    pub fn long_weighted_sum_eq<CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        vars: &[Self], 
        base: &E::Fr, 
        total: &Self, 
        use_d_next: bool
    ) -> Result<bool, SynthesisError>
    {
        let mut acc_fr = E::Fr::one();
        let mut loc_coefs = Vec::with_capacity(4);
        let mut loc_vars = Vec::with_capacity(4);
        
        let mut minus_one = E::Fr::one();
        minus_one.negate();

        for var in vars.iter() {
            if loc_vars.len() < 4 {
                loc_coefs.push(acc_fr.clone());
                acc_fr.mul_assign(&base);
                loc_vars.push(var.clone());
            }
            else {
                // we have filled in the whole vector!
                let temp = AllocatedNum::quartic_lc_with_cnst(cs: &mut CS, coefs: &[E::Fr], vars: &[Self], cnst: &E::Fr)
                .push(minus_one.clone());
                let temp = AllocatedNum::quartic_lc_with_const(cs, &coeffs[..], &current_vars[..], &E::Fr::zero())?;
                coeffs = vec![E::Fr::one(), acc_fr.clone()];
                current_vars = vec![temp, var.clone()];
                
                acc_fr.mul_assign(&base);
            }
        }

        if current_vars.len() == 4 {
            // we have filled in the whole vector!
            coeffs.push(minus_one.clone());
            let temp = AllocatedNum::quartic_lc_with_const(cs, &coeffs[..], &current_vars[..], &E::Fr::zero())?;
            coeffs = vec![E::Fr::one()];
            current_vars = vec![temp];
        }

        // pad with dummy variables
        for _i in current_vars.len()..3 {
            current_vars.push(AllocatedNum::alloc_zero(cs)?);
            coeffs.push(E::Fr::zero());
        }

        AllocatedNum::ternary_lc_with_const_eq_with_positions(cs, &coeffs[..], &current_vars[..], &E::Fr::zero(), total)?;
        Ok(())
    }

    pub fn long_weighted_sum_eq_with_d_next<CS: ConstraintSystem<E>>(
        cs: &mut CS, vars: &[Self], base: &E::Fr, total: &Self
    ) -> Result<bool, SynthesisError>
    {
        let mut acc_fr = E::Fr::one();
        let mut coeffs = Vec::with_capacity(5);
        let mut current_vars = Vec::with_capacity(4);

        let mut minus_one = E::Fr::one();
        minus_one.negate();
       
        for var in vars.iter() {
            if current_vars.len() < 4 {
                coeffs.push(acc_fr.clone());
                acc_fr.mul_assign(&base);
                current_vars.push(var.clone());
            }
            else {
                coeffs.push(minus_one.clone());
                let temp = AllocatedNum::quartic_lc_with_const(cs, &coeffs[..], &current_vars[..], &E::Fr::zero())?;
                coeffs = vec![E::Fr::one(), acc_fr.clone()];
                current_vars = vec![temp, var.clone()];
                
                acc_fr.mul_assign(&base);
            }
        }

        let use_d_next = if current_vars.len() == 4 {
            AllocatedNum::garbage(cs, &coeffs[..], &current_vars[..], &total)?;
            true
        }
        else {
            // pad with dummy variables
            for _i in current_vars.len()..3 {
                current_vars.push(AllocatedNum::alloc_zero(cs)?);
                coeffs.push(E::Fr::zero());
            }

            AllocatedNum::ternary_lc_with_const_eq_with_positions(cs, &coeffs[..], &current_vars[..], &E::Fr::zero(), total)?;
            false
        };

        Ok(use_d_next)
    }   
}


#[derive(Clone)]
pub enum Num<E: Engine> {
    Allocated(AllocatedNum<E>),
    Constant(E::Fr),
}

impl<E: Engine> Default for Num<E> {
    fn default() -> Self {
        Num::Constant(E::Fr::zero())
    }
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

    pub fn get_variable(&self) -> Option<AllocatedNum<E>> 
    {
        match self {
            Num::Constant(_) => None,
            Num::Allocated(var) => Some(var.clone()),
        }
    }

    pub fn eq<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<(), SynthesisError>
    {
        match (self, other) {
            (Num::Allocated(x), Num::Allocated(y)) => x.eq(cs, y.clone())?,
            (Num::Allocated(x), Num::Constant(fr)) | (Num::Constant(fr), Num::Allocated(x)) => todo!(),
            (Num::Constant(fr1), Num::Constant(fr2)) => {
                println!("left: {}, right: {}", fr1, fr2);
                assert_eq!(*fr1, *fr2);
            },
        }
        Ok(())
    }

    pub fn add<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError>
    {
        let res = match (self, other) {
            (Num::Constant(x), Num::Constant(y)) => {
                let mut temp = *x;
                temp.add_assign(y);
                Num::Constant(temp)
            },
            (Num::Allocated(var), Num::Constant(constant)) | (Num::Constant(constant), Num::Allocated(var)) => {
                let mut value = None;

                let addition_result = cs.alloc(|| {
                    let mut tmp = *var.value.get()?;
                    tmp.add_assign(&constant);
                    value = Some(tmp);
                    Ok(tmp)
                })?;

                let self_term = ArithmeticTerm::from_variable(var.variable);
                let other_term = ArithmeticTerm::constant(*constant);
                let result_term = ArithmeticTerm::from_variable(addition_result);
                let mut term = MainGateTerm::new();
                term.add_assign(self_term);
                term.add_assign(other_term);
                term.sub_assign(result_term);

                cs.allocate_main_gate(term)?;

                Num::Allocated(AllocatedNum {
                    value: value,
                    variable: addition_result
                })
            },
            (Num::Allocated(var1), Num::Allocated(var2)) => {
                let mut value = None;

                let addition_result = cs.alloc(|| {
                    let mut tmp = *var1.value.get()?;
                    let tmp2 = *var2.value.get()?;
                    tmp.add_assign(&tmp2);
                    value = Some(tmp);
                    Ok(tmp)
                })?;

                let self_term = ArithmeticTerm::from_variable(var1.variable);
                let other_term = ArithmeticTerm::from_variable(var2.variable);
                let result_term = ArithmeticTerm::from_variable(addition_result);
                let mut term = MainGateTerm::new();
                term.add_assign(self_term);
                term.add_assign(other_term);
                term.sub_assign(result_term);

                cs.allocate_main_gate(term)?;

                Num::Allocated(AllocatedNum {
                    value: value,
                    variable: addition_result
                })
            },
        };

        Ok(res)
    }

    pub fn add_two<CS: ConstraintSystem<E>>(&self, cs: &mut CS, first: &Self, second: &Self) -> Result<Self, SynthesisError>
    {
        let res = match (self, first, second) {
            (Num::Constant(x), Num::Constant(y), Num::Constant(z)) => {
                let mut temp = *x;
                temp.add_assign(y);
                temp.add_assign(z);
                Num::Constant(temp)
            },
            (Num::Allocated(var), Num::Constant(cnst1), Num::Constant(cnst2)) | 
            (Num::Constant(cnst1), Num::Allocated(var), Num::Constant(cnst2)) |
            (Num::Constant(cnst1), Num::Constant(cnst2), Num::Allocated(var)) => {
                let mut value = None;

                let addition_result = cs.alloc(|| {
                    let mut tmp = *var.value.get()?;
                    tmp.add_assign(&cnst1);
                    tmp.add_assign(&cnst2);
                    value = Some(tmp);
                    Ok(tmp)
                })?;

                let self_term = ArithmeticTerm::from_variable(var.variable);
                let mut constant = *cnst1;
                constant.add_assign(cnst2);
                let other_term = ArithmeticTerm::constant(constant);
                let result_term = ArithmeticTerm::from_variable(addition_result);
                let mut term = MainGateTerm::new();
                term.add_assign(self_term);
                term.add_assign(other_term);
                term.sub_assign(result_term);

                cs.allocate_main_gate(term)?;

                Num::Allocated(AllocatedNum {
                    value: value,
                    variable: addition_result
                })
            },
            (Num::Allocated(var1), Num::Allocated(var2), Num::Constant(constant)) |
            (Num::Allocated(var1), Num::Constant(constant), Num::Allocated(var2)) |
            (Num::Constant(constant), Num::Allocated(var1), Num::Allocated(var2)) => {
                let mut value = None;

                let addition_result = cs.alloc(|| {
                    let mut tmp = *var1.value.get()?;
                    let tmp2 = *var2.value.get()?;
                    tmp.add_assign(&tmp2);
                    tmp.add_assign(constant);
                    value = Some(tmp);
                    Ok(tmp)
                })?;

                let self_term = ArithmeticTerm::from_variable(var1.variable);
                let other_term = ArithmeticTerm::from_variable(var2.variable);
                let constant_term = ArithmeticTerm::constant(*constant);
                let result_term = ArithmeticTerm::from_variable(addition_result);
                let mut term = MainGateTerm::new();
                term.add_assign(self_term);
                term.add_assign(other_term);
                term.add_assign(constant_term);
                term.sub_assign(result_term);

                cs.allocate_main_gate(term)?;

                Num::Allocated(AllocatedNum {
                    value: value,
                    variable: addition_result
                })
            },
            (Num::Allocated(var1), Num::Allocated(var2), Num::Allocated(var3)) => {
                let mut value = None;

                let addition_result = cs.alloc(|| {
                    let mut tmp = *var1.value.get()?;
                    let tmp2 = *var2.value.get()?;
                    let tmp3 = *var3.value.get()?;
                    tmp.add_assign(&tmp2);
                    tmp.add_assign(&tmp3);
                    value = Some(tmp);
                    Ok(tmp)
                })?;

                let self_term = ArithmeticTerm::from_variable(var1.variable);
                let other_term = ArithmeticTerm::from_variable(var2.variable);
                let third_term = ArithmeticTerm::from_variable(var3.variable);
                let result_term = ArithmeticTerm::from_variable(addition_result);
                let mut term = MainGateTerm::new();
                term.add_assign(self_term);
                term.add_assign(other_term);
                term.add_assign(third_term);
                term.sub_assign(result_term);

                cs.allocate_main_gate(term)?;

                Num::Allocated(AllocatedNum {
                    value: value,
                    variable: addition_result
                })
            },
        };

        Ok(res)
    }

    pub fn lc<CS: ConstraintSystem<E>>(cs: &mut CS, input_coeffs: &[E::Fr], inputs: &[Num<E>]) -> Result<Self, SynthesisError>
    {
        assert_eq!(input_coeffs.len(), inputs.len());

        // corner case: all our values are actually constants
        if inputs.iter().all(| x | x.is_constant()) {
            let value = inputs.iter().zip(input_coeffs.iter()).fold(E::Fr::zero(), |acc, (x, coef)| {
                let mut temp = x.get_value().unwrap();
                temp.mul_assign(&coef);
                temp.add_assign(&acc);
                temp
            });

            return Ok(Num::Constant(value));
        }

        // okay, from now one we may be sure that we have at least one allocated term
        let mut constant_term = E::Fr::zero();
        let mut vars = Vec::with_capacity(4);
        let mut coeffs = Vec::with_capacity(5);
        let mut res_var = AllocatedNum::alloc_zero(cs)?;

        // Note: the whole thing may be a little more efficient with the use of custom gates
        // exploiting (d_next)
        let mut minus_one = E::Fr::one();
        minus_one.negate();

        for (x, coef) in inputs.iter().zip(input_coeffs.iter()) {
            match x {
                Num::Constant(x) => {
                    let mut temp = x.clone();
                    temp.mul_assign(&coef);
                    constant_term.add_assign(&temp);
                },
                Num::Allocated(x) => {
                    if vars.len() < 4 
                    {
                        vars.push(x.clone());
                        coeffs.push(coef.clone());
                    }
                    else {
                        coeffs.push(minus_one.clone());
                        res_var = AllocatedNum::quartic_lc_with_const(cs, &coeffs[..], &vars[..], &constant_term)?;

                        constant_term = E::Fr::zero();
                        vars = vec![res_var, x.clone()];
                        coeffs = vec![E::Fr::one(), coef.clone()];
                    }
                }
            }
        }

        if vars.len() == 4 {
            //println!("OPTIMIZE2");
            coeffs.push(minus_one.clone());
            res_var = AllocatedNum::quartic_lc_with_const(cs, &coeffs[..], &vars[..], &constant_term)?;

            constant_term = E::Fr::zero();
            vars = vec![res_var];
            coeffs = vec![E::Fr::one()];
        }

        // pad with dummy variables
        for _i in vars.len()..3 {
            vars.push(AllocatedNum::alloc_zero(cs)?);
            coeffs.push(E::Fr::zero());
        }

        let res_var = AllocatedNum::alloc(cs, || {
            let mut cur = E::Fr::zero();
            for (elem, coef) in inputs.iter().zip(input_coeffs.iter()) {
                let mut tmp = elem.get_value().grab()?;
                tmp.mul_assign(coef);
                cur.add_assign(&tmp);
            }
            Ok(cur)
        })?;
        
        AllocatedNum::ternary_lc_with_const_eq_with_positions(cs, &coeffs[..], &vars[..], &constant_term, &res_var)?;
        Ok(Num::Allocated(res_var))
    }

    // same as lc but with all the coefficients set to be 1
    pub fn sum<CS: ConstraintSystem<E>>(cs: &mut CS, nums: &[Num<E>]) -> Result<Self, SynthesisError>
    {
        let coeffs = vec![E::Fr::one(); nums.len()];
        Self::lc(cs, &coeffs[..], &nums[..])
    }

    // for given array of slices : [x0, x1, x2, ..., xn] of arbitrary length, base n and total accumulated x
    // validates that x = x0 + x1 * base + x2 * base^2 + ... + xn * base^n
    pub fn long_weighted_sum<CS>(cs: &mut CS, vars: &[Self], base: &E::Fr) -> Result<Self, SynthesisError>
    where CS: ConstraintSystem<E>
    {
        let mut coeffs = Vec::with_capacity(vars.len());
        let mut acc = E::Fr::one();

        for _ in 0..vars.len() {
            coeffs.push(acc.clone());
            acc.mul_assign(&base);
        }

        Self::lc(cs, &coeffs[..], vars)
    }
}