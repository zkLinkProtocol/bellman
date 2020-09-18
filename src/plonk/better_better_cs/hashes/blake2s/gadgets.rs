use crate::plonk::better_better_cs::cs::*;
use crate::plonk::better_better_cs::lookup_tables::*;
use crate::plonk::better_better_cs::utils;
use crate::pairing::ff::*;
use crate::pairing::ff::{PrimeField, PrimeFieldRepr};
use crate::SynthesisError;
use crate::Engine;
use crate::plonk::better_better_cs::gadgets::num::{
    AllocatedNum,
    Num,
};

use super::tables::*;
use crate::plonk::better_better_cs::gadgets::assignment::{
    Assignment
};
use std::sync::Arc;
use splitmut::SplitMut;
use std::{ iter, mem };

type Result<T> = std::result::Result<T, SynthesisError>;

const CHUNK_SIZE : usize = 8; 
const SHIFT : usize = 4;
const SPLIT_POINT : usize = 7; 

// returns n ^ exp if exp is not zero, n otherwise
fn u64_exp_to_ff<Fr: PrimeField>(n: u64, exp: u64) -> Fr {
    let mut repr : <Fr as PrimeField>::Repr = Fr::zero().into_repr();
    repr.as_mut()[0] = n;
    let mut res = Fr::from_repr(repr).expect("should parse");

    if exp != 0 {
        res = res.pow(&[exp]);
    }

    res
}

fn u64_to_ff<Fr: PrimeField>(n: u64) -> Fr {
    u64_exp_to_ff::<Fr>(n, 0)
}


impl From<splitmut::SplitMutError> for SynthesisError {
    fn from(_splitmut_err: splitmut::SplitMutError) -> SynthesisError {
        SynthesisError::UnexpectedIdentity
    }
}


pub trait IdentifyFirstLast: Iterator + Sized {
    fn identify_first_last(self) -> Iter<Self>;
}

impl<I> IdentifyFirstLast for I where I: Iterator {
    fn identify_first_last(self) -> Iter<Self> {
        Iter(true, self.peekable())
    }
}

pub struct Iter<I>(bool, iter::Peekable<I>) where I: Iterator;

impl<I> Iterator for Iter<I> where I: Iterator {
    type Item = (bool, bool, I::Item);

    fn next(&mut self) -> Option<Self::Item> {
        let first = mem::replace(&mut self.0, false);
        self.1.next().map(|e| (first, self.1.peek().is_none(), e))
    }
}


#[derive(Clone)]
pub struct DecomposedRegister<E : Engine> {
    pub arr : [Num<E>; 4]
}

impl<E: Engine> Default for DecomposedRegister<E> {
    fn default() -> Self {
        DecomposedRegister {
            arr: [Num::default(), Num::default(), Num::default(), Num::default()],
        }
    }
}


#[derive(Clone)]
pub struct Register<E: Engine> {
    full: (bool, Num<E>),
    decomposed: (bool, DecomposedRegister<E>),
}

impl<E: Engine> Default for Register<E> {
    fn default() -> Self {
        Register {
            full : (true, Num::default()),
            decomposed: (true, DecomposedRegister::default()),
        }
    }
}

impl<E: Engine> Register<E> {
    pub fn is_full_form_available(&self) -> bool {
        self.full.0
    }
    
    pub fn is_decomposed_form_available(&self) -> bool {
        self.decomposed.0
    }

    pub fn is_const(&mut self) -> bool {
        if self.is_full_form_available() && self.full.1.is_constant() {
            return true;
        }
        else {
            assert_eq!(self.is_decomposed_form_available(), true);
            if self.decomposed.1.arr.iter().all(|x| x.is_constant()) {
                self.full.0 = true;
                let base = u64_to_ff(1 << 8);
                
                let mut sum = self.decomposed.1.arr[3].get_value().unwrap();
                sum.mul_assign(&base);
                sum.add_assign(&self.decomposed.1.arr[2].get_value().unwrap());
                sum.mul_assign(&base);
                sum.add_assign(&self.decomposed.1.arr[1].get_value().unwrap());
                sum.mul_assign(&base);
                sum.add_assign(&self.decomposed.1.arr[0].get_value().unwrap());

                self.full.1 = Num::Constant(sum);
                return true;
            }
        }
        return false;
    }
}

impl<E: Engine> From<Num<E>> for Register<E> 
{
    fn from(num: Num<E>) -> Self {
        Register {
            full: (true, num),
            decomposed: (false, DecomposedRegister::default()),
        }
    }
}

impl<E: Engine> From<DecomposedRegister<E>> for Register<E> 
{
    fn from(decomposed: DecomposedRegister<E>) -> Self {
        Register {
            full: (false, Num::default()),
            decomposed: (true, decomposed),
        }
    }
}


pub struct RegisterFile<E: Engine> {
    regs : Vec<Register<E>>,
}


pub struct Blake2sGadget<E: Engine> {
    xor_table: Arc<LookupTableApplication<E>>,
    xor_rotate_table4: Arc<LookupTableApplication<E>>,
    xor_rotate_table7: Arc<LookupTableApplication<E>>,
    //split_table: Arc<LookupTableApplication<E>>,
    iv: [Register<E>; 8],
    sigmas : [[usize; 16]; 10],
}

impl<E: Engine> Blake2sGadget<E> {
   
    pub fn new<CS: ConstraintSystem<E>>(cs: &mut CS) -> Result<Self> {
        let columns3 = vec![
            PolyIdentifier::VariablesPolynomial(0), 
            PolyIdentifier::VariablesPolynomial(1), 
            PolyIdentifier::VariablesPolynomial(2)
        ];

        let name1: &'static str = "xor_table";
        let xor_table = LookupTableApplication::new(
            name1,
            XorTable::new(CHUNK_SIZE, name1),
            columns3.clone(),
            true
        );

        // let name2 : &'static str = "compound_shift_table";
        // let compound_shift_table = LookupTableApplication::new(
        //     name2,
        //     CompoundShiftTable::new(CHUNK_SIZE, SHIFT, name2),
        //     columns3.clone(),
        //     true
        // );

        let name2 : &'static str = "xor_rotate_table4";
        let xor_rotate_table4 = LookupTableApplication::new(
            name2,
            XorRotateTable::new(CHUNK_SIZE, 4, name2),
            columns3.clone(),
            true
        );

        let name3 : &'static str = "xor_rotate_table7";
        let xor_rotate_table7 = LookupTableApplication::new(
            name3,
            XorRotateTable::new(CHUNK_SIZE, 7, name3),
            columns3.clone(),
            true
        );

        // let name3 : &'static str = "split_table";
        // let split_table = LookupTableApplication::new(
        //     name3,
        //     SplitTable::new(CHUNK_SIZE, SPLIT_POINT, name3),
        //     columns3.clone(),
        //     true
        // );

        let xor_table = cs.add_table(xor_table)?;
        //let compound_shift_table = cs.add_table(compound_shift_table)?;
        let xor_rotate_table4 = cs.add_table(xor_rotate_table4)?;
        let xor_rotate_table7 = cs.add_table(xor_rotate_table7)?;
        //let split_table  = cs.add_table(split_table)?;

        let iv = [
            Num::Constant(u64_to_ff(0x6A09E667 ^ 0x01010000)).into(), Num::Constant(u64_to_ff(0xBB67AE85)).into(), 
            Num::Constant(u64_to_ff(0x3C6EF372)).into(), Num::Constant(u64_to_ff(0xA54FF53A)).into(),
            Num::Constant(u64_to_ff(0x510E527F)).into(), Num::Constant(u64_to_ff(0x9B05688C)).into(), 
            Num::Constant(u64_to_ff(0x1F83D9AB)).into(), Num::Constant(u64_to_ff(0x5BE0CD19)).into(),
        ];

        let sigmas: [[usize; 16]; 10] = [
            [ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 ],
            [ 14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3 ],
            [ 11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4 ],
            [ 7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8 ],
            [ 9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13 ],
            [ 2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9 ],
            [ 12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11 ],
            [ 13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10 ],
            [ 6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5 ],
            [ 10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0 ]
        ];

        Ok(Blake2sGadget {
            xor_table,
            xor_rotate_table4,
            xor_rotate_table7,
            //split_table,
            iv,
            sigmas,
        })
    }

    fn query_table_internal<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS, 
        table: &Arc<LookupTableApplication<E>>, 
        key1: &AllocatedNum<E>,
        key2: &AllocatedNum<E>,
    ) -> Result<AllocatedNum<E>> 
    {
        let res = match (key1.get_value(), key2.get_value()) {
            (Some(val1), Some(val2)) => {
                let new_val = table.query(&[val1, val2])?;
                AllocatedNum::alloc(cs, || Ok(new_val[0]))?
            },
            (_, _) => AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?        
        };

        let vars = [key1.get_variable(), key2.get_variable(), res.get_variable(), key1.get_variable()];

        cs.begin_gates_batch_for_step()?;
        cs.allocate_variables_without_gate(&vars, &[])?;
        cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;
        cs.end_gates_batch_for_step()?;
        
        Ok(res)
    }

    fn query_table<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS, 
        table: &Arc<LookupTableApplication<E>>,
        shift: usize, 
        key1: &Num<E>,
        key2: &Num<E>,
    ) -> Result<Num<E>> 
    {
        let res = match (key1, key2) {
            (Num::Allocated(x), Num::Allocated(y)) => {
                let new_var = self.query_table_internal(cs, table, &x, &y)?;
                Num::Allocated(new_var)
            },
            (Num::Constant(x), Num::Constant(y)) => {
                let f_repr = x.into_repr();
                let left = f_repr.as_ref()[0]; 
                let f_repr = y.into_repr();
                let right = f_repr.as_ref()[0]; 

                let mut n = left ^ right;
                n = if shift > 0 {(n >> shift) + ((n << (32 - shift)) & 0xffffffff) } else {n};

                let new_cnst = u64_to_ff(n);
                Num::Constant(new_cnst)
            },
            (Num::Allocated(var), Num::Constant(cnst)) | (Num::Constant(cnst), Num::Allocated(var)) => {
                let cnst_var = AllocatedNum::alloc_cnst(cs, *cnst)?;
                let new_var = self.query_table_internal(cs, table, &var, &cnst_var)?;
                Num::Allocated(new_var)
            }
        };

        Ok(res)
    }


    fn range_check<CS: ConstraintSystem<E>>(&self, cs: &mut CS, var: &AllocatedNum<E>) -> Result<()> {
        let dummy = AllocatedNum::alloc_zero(cs)?;
        let _unused = self.query_table_internal(cs, &self.xor_table, var, &dummy)?;
        Ok(())
    }

    fn get_full<CS: ConstraintSystem<E>>(&self, cs: &mut CS, reg: &mut Register<E>) -> Result<Num<E>> {
        if !reg.is_full_form_available() {
            reg.full.0 = true;
            reg.full.1 = Num::long_weighted_sum(cs, &reg.decomposed.1.arr[..], &u64_to_ff(1 << 8))?;
        };

        Ok(reg.full.1.clone())
    }

    fn get_decomposed<CS: ConstraintSystem<E>>(&self, cs: &mut CS, reg: &mut Register<E>) -> Result<DecomposedRegister<E>> {
        if !reg.is_decomposed_form_available() {
            reg.decomposed.0 = true;
            match &reg.full.1 {
                Num::Constant(fr) => {
                    let f_repr = fr.into_repr();
                    let n = f_repr.as_ref()[0];

                    for i in 0..4 {
                        let m = (n >> (8 * i)) & ((1 << 8) - 1);
                        reg.decomposed.1.arr[i] = Num::Constant(u64_to_ff(m));
                    }
                },
                Num::Allocated(var) => {
                    match var.get_value() {
                        None => {
                            for i in 0..4 {
                                let new_var = AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?;
                                reg.decomposed.1.arr[i] = Num::Allocated(new_var);
                            } 
                        },
                        Some(fr) => {
                            let f_repr = fr.into_repr();
                            let n = f_repr.as_ref()[0];

                            for i in 0..4 {
                                let m = (n >> (8 * i)) & ((1 << 8) - 1);
                                let new_var = AllocatedNum::alloc(cs, || Ok(u64_to_ff(m)))?;
                                reg.decomposed.1.arr[i] = Num::Allocated(new_var);
                            }
                        }
                    }
                }
            }
        }

        Ok(reg.decomposed.1.clone())
    }

    fn add2<CS: ConstraintSystem<E>>(&self, cs: &mut CS, reg1: &mut Register<E>, reg2: &mut Register<E>) -> Result<Num<E>> {
        // res + of * 2^32 = reg1 + reg2;
        // check that of is small here
        // range check for res will be later
        let x = self.get_full(cs, reg1)?;
        let y = self.get_full(cs, reg2)?;

        let res = match (&x, &y) {
            (Num::Constant(fr1), Num::Constant(fr2)) => {
                let mut temp = fr1.clone();
                temp.add_assign(&fr2);
                let f_repr = temp.into_repr();
                let n = f_repr.as_ref()[0] >> 32;
                Num::Constant(u64_to_ff(n))
            },
            (_, _) => {
                let fr1 = x.get_value();
                let fr2 = y.get_value();
                let of_val = match (fr1, fr2) {
                    (Some(fr1), Some(fr2)) => {
                        let mut temp = fr1.clone();
                        temp.add_assign(&fr2);
                        let f_repr = temp.into_repr();
                        let n = f_repr.as_ref()[0] >> 32;
                        Some(u64_to_ff(n))
                    },
                    (_, _) => None,
                };

                let of_var = AllocatedNum::alloc(cs, || of_val.grab())?;
                self.range_check(cs, &of_var)?;
                let of = Num::Allocated(of_var);
                
                let one = E::Fr::one();
                let mut coef : E::Fr = u64_to_ff(1 << 32);
                coef.negate();
                let res = Num::lc(cs, &[one.clone(), one, coef], &[x, y, of])?;
                
                res
            },
        };

        Ok(res)
    }

    fn add3<CS>(&self, cs: &mut CS, reg1: &mut Register<E>, reg2: &mut Register<E>, reg3: &mut Register<E>) -> Result<Num<E>> 
    where CS: ConstraintSystem<E>
    {
        let x = self.get_full(cs, reg1)?;
        let y = self.get_full(cs, reg2)?;
        let z = self.get_full(cs, reg3)?;

        let res = match (&x, &y, &z) {
            (Num::Constant(fr1), Num::Constant(fr2), Num::Constant(fr3)) => {
                let mut temp = fr1.clone();
                temp.add_assign(&fr2);
                temp.add_assign(&fr3);
                let f_repr = temp.into_repr();
                let n = f_repr.as_ref()[0] >> 32;
                Num::Constant(u64_to_ff(n))
            },
            (_, _, _) => {
                let fr1 = x.get_value();
                let fr2 = y.get_value();
                let fr3 = y.get_value();
                let of_val = match (fr1, fr2, fr3) {
                    (Some(fr1), Some(fr2), Some(fr3)) => {
                        let mut temp = fr1.clone();
                        temp.add_assign(&fr2);
                        temp.add_assign(&fr3);
                        let f_repr = temp.into_repr();
                        let n = f_repr.as_ref()[0] >> 32;
                        Some(u64_to_ff(n))
                    },
                    (_, _, _) => None,
                };
                
                let of_var = AllocatedNum::alloc(cs, || of_val.grab())?;
                self.range_check(cs, &of_var)?;
                let of = Num::Allocated(of_var);
                
                let one = E::Fr::one();
                let mut coef : E::Fr = u64_to_ff(1 << 32);
                coef.negate();
                let res = Num::lc(cs, &[one.clone(), one.clone(), one, coef], &[x, y, z, of])?;
                res
            },
        };

        Ok(res)
    }

    fn G<CS: ConstraintSystem<E>>(
        &self, 
        cs: &mut CS, 
        v: &mut RegisterFile<E>, 
        a: usize, b: usize, c: usize, d: usize,
        t0: &Num<E>, t1: &Num<E>, 
    ) -> Result<()>
    {
        let mut temp_arr = <[Num<E>; 4]>::default();
        let mut z = v.regs.get_muts();
        let a = z.at(a)?;
        let b = z.at(b)?;
        let c = z.at(c)?;
        let d = z.at(d)?;

        let mut t0 : Register<E> = t0.clone().into();
        let mut t1 : Register<E> = t1.clone().into();
        
        // v[a] := (v[a] + v[b] + x) mod 2**w
        *a = self.add3(cs, a, b, &mut t0)?.into();

        // v[d] := (v[d] ^ v[a]) >>> 16
        let x = self.get_decomposed(cs, a)?;
        let y = self.get_decomposed(cs, d)?;
        for i in 0..4 {
            temp_arr[i] = self.query_table(cs, &self.xor_table, 0, &x.arr[i], &y.arr[i])?;
        }
        let new_val = DecomposedRegister { 
            arr: [temp_arr[2].clone(), temp_arr[3].clone(), temp_arr[0].clone(), temp_arr[1].clone()]
        };
        *d = new_val.into();

        // v[c] := (v[c] + v[d]) mod 2**w
        *c = self.add2(cs, c, d)?.into();
        
        // v[b] := (v[b] ^ v[c]) >>> 12
        let x = self.get_decomposed(cs, b)?;
        let y = self.get_decomposed(cs, c)?;
        temp_arr[1] = self.query_table(cs, &self.xor_rotate_table4, 4, &x.arr[1], &y.arr[1])?;
        temp_arr[0] = self.query_table(cs, &self.xor_table, 0, &x.arr[0], &y.arr[0])?;
        temp_arr[2] = self.query_table(cs, &self.xor_table, 0, &x.arr[2], &y.arr[2])?;
        temp_arr[3] = self.query_table(cs, &self.xor_table, 0, &x.arr[3], &y.arr[3])?;
    
        let new_val = Num::lc(
            cs, 
            &[E::Fr::one(), u64_to_ff(1 << 4), u64_to_ff(1 << 12), u64_to_ff(1 << 20)], 
            &[temp_arr[1].clone(), temp_arr[2].clone(), temp_arr[3].clone(), temp_arr[0].clone()],
        )?;
        *b = new_val.into();

        // v[a] := (v[a] + v[b] + y) mod 2**w
        *a = self.add3(cs, a, b, &mut t1)?.into();

        // v[d] := (v[d] ^ v[a]) >>> 8
        let x = self.get_decomposed(cs, a)?;
        let y = self.get_decomposed(cs, d)?;
        for i in 0..4 {
            temp_arr[i] = self.query_table(cs, &self.xor_table, 0, &x.arr[i], &y.arr[i])?;
        }
        let new_val = DecomposedRegister { 
            arr: [temp_arr[1].clone(), temp_arr[2].clone(), temp_arr[3].clone(), temp_arr[0].clone()]
        };
        *d = new_val.into();
        
        // v[c] := (v[c] + v[d]) mod 2**w
        *c = self.add2(cs, c, d)?.into();

        // v[b] := (v[b] ^ v[c]) >>> 7
        let x = self.get_decomposed(cs, b)?;
        let y = self.get_decomposed(cs, c)?;
        temp_arr[0] = self.query_table(cs, &self.xor_rotate_table7, 7, &x.arr[0], &y.arr[0])?;
        for i in 1..4 {
            temp_arr[i] = self.query_table(cs, &self.xor_table, 0, &x.arr[i], &y.arr[i])?;
        }
        let new_val = Num::lc(
            cs, 
            &[E::Fr::one(), u64_to_ff(1 << 1), u64_to_ff(1 << 9), u64_to_ff(1 << 17)], 
            &temp_arr[..],
        )?;
        *b = new_val.into();

        Ok(())
    }

    fn apply_xor_with_const<CS: ConstraintSystem<E>>(&self, cs: &mut CS, reg: &mut Register<E>, cnst: u64) -> Result<()>
    {
        if reg.is_const() {
            let temp = reg.full.1.get_value().unwrap();
            let f_repr = temp.into_repr();
            let n = f_repr.as_ref()[0];
            let new_val = u64_to_ff(n ^ cnst);
            *reg = Num::Constant(new_val).into();
        }
        else {
            let mut x = self.get_decomposed(cs, reg)?;
            for i in 0..4 {
                let byte_val = (cnst >> 8 * i) & 0xff;
                if byte_val != 0 {
                    let cnst_var = AllocatedNum::alloc_cnst(cs, u64_to_ff(byte_val))?;
                    x.arr[i] = self.query_table(cs, &self.xor_table, 0, &x.arr[i], &Num::Allocated(cnst_var))?;
                }
            }
            *reg = x.into();
        }

        Ok(())
    }

    fn F<CS>(
        &self, cs: &mut CS, mut hash_state: RegisterFile<E>, m: &[Num<E>], total_len: u64, last_block: bool,
    ) -> Result<RegisterFile<E>>
    where CS: ConstraintSystem<E>
    {
        // Initialize local work vector v[0..15]
        let mut v = RegisterFile { regs: Vec::with_capacity(16) };
        // First half from state.
        for i in 0..8 {
            v.regs.push(hash_state.regs[i].clone());
        }
        // Second half from IV.
        for i in 0..8 {
            v.regs.push(self.iv[i].clone());
        }

        self.apply_xor_with_const(cs, &mut v.regs[12], total_len & 0xffffffff)?; // Low word of the offset.
        self.apply_xor_with_const(cs, &mut v.regs[13], total_len >> 32)?; // High word.

        if last_block {
            self.apply_xor_with_const(cs, &mut v.regs[14], 0xffffffff)?; // Invert all bits.
        }    
              
        // Cryptographic mixing: ten rounds
        for i in 0..10 {
            // Message word selection permutation for this round.
            let s = &self.sigmas[i];

            self.G(cs, &mut v, 0, 4, 8, 12, &m[s[0]], &m[s[1]])?;
            self.G(cs, &mut v, 1, 5, 9, 13, &m[s[2]], &m[s[3]])?;
            self.G(cs, &mut v, 2, 6, 10, 14, &m[s[4]], &m[s[5]])?;
            self.G(cs, &mut v, 3, 7, 11, 15, &m[s[6]], &m[s[7]])?;
            self.G(cs, &mut v, 0, 5, 10, 15, &m[s[8]], &m[s[9]])?;
            self.G(cs, &mut v, 1, 6, 11, 12, &m[s[10]], &m[s[11]])?;
            self.G(cs, &mut v, 2, 7, 8, 13, &m[s[12]], &m[s[13]])?;
            self.G(cs, &mut v, 3, 4, 9, 14, &m[s[14]], &m[s[15]])?;
        }

        // XOR the two halves.
        let mut res = RegisterFile { regs: Vec::with_capacity(8) };
        let mut h = hash_state.regs.get_muts();
        let mut v = v.regs.get_muts();

        for i in 0..8 {
            // h[i] := h[i] ^ v[i] ^ v[i + 8]
            let x = self.get_decomposed(cs, h.at(i)?)?;
            let y = self.get_decomposed(cs, v.at(i)?)?;
            let z = self.get_decomposed(cs, v.at(i+8)?)?;
            let mut new_state = DecomposedRegister::default();
            
            for i in 0..4 {
                let tmp = self.query_table(cs, &self.xor_table, 0, &x.arr[i], &y.arr[i])?;
                new_state.arr[i] = self.query_table(cs, &self.xor_table, 0, &tmp, &z.arr[i])?;
            }

            res.regs.push(new_state.into());
        }

        Ok(res)
    }

    pub fn digest<CS: ConstraintSystem<E>>(&self, cs: &mut CS, data: &[Num<E>]) -> Result<Vec<Num<E>>> 
    {
        // h[0..7] := IV[0..7] // Initialization Vector.
        let mut total_len : u64 = 0;
        let mut hash_state = RegisterFile { regs: Vec::with_capacity(8) };
        for i in 0..8 {
            hash_state.regs.push(self.iv[i].clone());
        }

        for (_is_first, is_last, block) in data.chunks(16).identify_first_last() 
        {
            assert_eq!(block.len(), 16);
            total_len += 64;
            hash_state = self.F(cs, hash_state, &block[..], total_len, is_last)?;
        }

        let mut res = Vec::with_capacity(8);
        for i in 0..8 {
            res.push(self.get_full(cs, &mut hash_state.regs[0])?);
        }
        Ok(res)
    }
}
