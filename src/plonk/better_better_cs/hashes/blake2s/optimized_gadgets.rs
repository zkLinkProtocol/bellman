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
use std::collections::HashMap;
use std::cell::Cell;

type Result<T> = std::result::Result<T, SynthesisError>;

const CHUNK_SIZE : usize = 8; 
const SHIFT4 : usize = 4;
const SHIFT7 : usize = 7; 
const BLAKE2s_STATE_WIDTH : usize = 16;


impl From<splitmut::SplitMutError> for SynthesisError {
    fn from(_splitmut_err: splitmut::SplitMutError) -> SynthesisError {
        // TODO: create special error for this sort of things
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
pub struct DecomposedNum<E : Engine> {
    r0: Num<E>,
    r1: Num<E>,
    r2: Num<E>,
    r3: Num<E>,
}

impl<E: Engine> Default for DecomposedNum<E> {
    fn default() -> Self {
        DecomposedNum {
            r0: Num::default(), 
            r1: Num::default(), 
            r2: Num::default(), 
            r3: Num::default(),
        }
    }
}

#[derive(Clone)]
pub struct Reg<E: Engine> {
    full: Num<E>,
    decomposed: DecomposedNum<E>,
}

impl<E: Engine> Default for Reg<E> {
    fn default() -> Self {
        Reg {
            full : Num::default(),
            decomposed: DecomposedNum::default(),
        }
    }
}


#[derive(Clone, Default)]
pub struct HashState<E: Engine>([Reg<E>; BLAKE2s_STATE_WIDTH]);


// the purpose of this (and the following) struct is explained in the comments of the main text
// all linear variables are represented in the form (bool, coef, var)
// where the boolean flag asserts that variable was actually assigned a value (for self-test and debugging assistance)
#[derive(Clone)]
pub struct GateVarHelper<E: Engine>{
    assigned: bool,
    coef: E::Fr,
    val: AllocatedNum<E>,
}

impl<E: Engine> Default for GateVarHelper<E> {
    fn default() -> Self {
        GateVarHelper {
            assigned: false,
            coef: E::Fr::zero(),
            val: AllocatedNum::default(),
        }
    }
}

#[derive(Clone)]
pub struct GateAllocHelper<E: Engine> {
    a: GateVarHelper<E>,
    b: GateVarHelper<E>,
    c: GateVarHelper<E>,
    d: GateVarHelper<E>,

    cnst_sel: E::Fr,
    d_next_sel: E::Fr,     
}

impl<E: Engine> Default for GateAllocHelper<E> {
    fn default() -> Self {
        GateAllocHelper {
            a: GateVarHelper::default(),
            b: GateVarHelper::default(),
            c: GateVarHelper::default(),
            d: GateVarHelper::default(),

            cnst_sel: E::Fr::zero(),
            d_next_sel: E::Fr::zero(), 
        }
    }
}


pub struct OptimizedBlake2sGadget<E: Engine> {
    xor_table: Arc<LookupTableApplication<E>>,
    compound_xor4_table: Arc<LookupTableApplication<E>>,
    compound_xor7_table: Arc<LookupTableApplication<E>>,
    
    iv: [u64; 8],
    iv0_twist: u64,
    sigmas : [[usize; 16]; 10],

    allocated_cnsts : Cell<HashMap<u64, AllocatedNum<E>>>,
}

impl<E: Engine> OptimizedBlake2sGadget<E> {

    fn u64_to_ff(&self, n: u64) -> E::Fr {
        let mut repr : <E::Fr as PrimeField>::Repr = E::Fr::zero().into_repr();
        repr.as_mut()[0] = n;
        let mut res = E::Fr::from_repr(repr).expect("should parse");
        res
    }
   
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

        let name2 : &'static str = "xor_rotate_table4";
        let xor_rotate_table4 = LookupTableApplication::new(
            name2,
            XorRotateTable::new(CHUNK_SIZE, SHIFT4, name2),
            columns3.clone(),
            true
        );

        let name3 : &'static str = "xor_rotate_table7";
        let xor_rotate_table7 = LookupTableApplication::new(
            name3,
            XorRotateTable::new(CHUNK_SIZE, SHIFT7, name3),
            columns3.clone(),
            true
        );

        let xor_table = cs.add_table(xor_table)?;
        let xor_rotate_table4 = cs.add_table(xor_rotate_table4)?;
        let xor_rotate_table7 = cs.add_table(xor_rotate_table7)?;

        let iv = [
            0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
            0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
        ];
        let twisted_iv_0 =  0x6A09E667 ^ 0x01010000 ^ 32;

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

        let allocated_cnsts = Cell::new(HashMap::new());

        Ok(Blake2sGadget {
            xor_table,
            xor_rotate_table4,
            xor_rotate_table7,

            iv,
            twisted_iv_0,
            sigmas,

            allocated_cnsts,
        })
    }

    fn query_table<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS, 
        table: &Arc<LookupTableApplication<E>>, 
        key1: &AllocatedNum<E>,
        key2: &AllocatedNum<E>,
        ph: &AllocatedNum<E>, // placeholder placer in d register
    ) -> Result<AllocatedNum<E>> 
    {
        let res = match (key1.get_value(), key2.get_value()) {
            (Some(val1), Some(val2)) => {
                let new_val = table.query(&[val1, val2])?;
                AllocatedNum::alloc(cs, || Ok(new_val[0]))?
            },
            (_, _) => AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?        
        };

        let vars = [key1.get_variable(), key2.get_variable(), res.get_variable(), ph.get_variable()];

        cs.begin_gates_batch_for_step()?;
        cs.allocate_variables_without_gate(&vars, &[])?;
        cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;
        cs.end_gates_batch_for_step()?;
        
        Ok(res)
    }

    // the trick, we are going to use is the following:
    // we may handle two range checks (for overflow flags of0 and of1) simultaneously, using only one table access
    // more precisely we form the row of variables: [of0, of1, of0 ^ of1, ph],
    // where ph - is a placeholder variable, which is not used on current row, but may be connected to previous row
    // via usage of d_next selector
    fn range_check<CS>(&self, cs: &mut CS, of0: &AllocatedNum<E>, of1: &AllocatedNum<E>, ph: &AllocatedNum<E>) -> Result<()> 
    where CS: ConstraintSystem<E>
    {
        let _unused = self.query_table(cs, &self.xor_table, of0, of1, ph)?;
        Ok(())
    }

    // first step of G function is handling equations of the form :
    // y = a + b + x (e.g. v[a] = v[a] + v[b] + x),
    // where a, b are available in both full and decomposed forms (in other words, are of type Reg)
    // and x is available only in full form (in other words, x is just a regular Num)
    // we want the result y to be represented in both full and decomposed forms

    // there are special cases which we want to handle separately:
    // 1) all of a, b, x - are constants: than there is actually nothing interesting,
    // no constraints will be allocated, just return the new constant

    // 2) all of a, b, x are variables: there will be 3 rows:
    // [y0, y1, y2, y3] - decomposed parts of resulted y: y = y0 + 2^8 * y1 + 2^16 * y2 + 2^24 * y3: 
    // [a, b, x, y] - where y = a + b + x - 2^32 * of (using of via d_next selector)
    // [of, t, of ^ t, of] - range check for of and t

    // 3) if we are in between these two corner cases we are going to use the sceme as in case (2), the only difference is that
    // we are going to replace all instances of costant variables with dummy placeholders and push them instead into constant selector
    // e.g: assume thta a - is variable (AllocatedVar) and b, x - are constants : than in any case y, of, y0, y1, y2, y3 -a re variables
    // and the second row will be replaced by: 
    // [a, dummy, dummy, y], and constant selector will contain the value of x + y
    // this identical approach to handling constant and variables is hidden under the GateAllocHelper facade
    
    // NB: there is inversion in computation: we first precompute the value of y and split it into corresponding
    // chunks y0, y1, y2, y3 BEFORE allocating contraint defining y itself! this inversion will be a recurring pattern 
    // in our optimization
    // also - there is a place for additional 8-bit variable t on the last row, so there is a possibility to multiplex two
    // oveflow checks on the same row: for current of and (yet unknown) t
    // and yes, we are going to explot the inversion trick again: we take t from overflow check of step 3!

    // due to such an extended use of inversion trick we have to split all equation generations it two phases: 
    // setup - where we aforehead define all variables and compute their values
    // and actual gate allocation

    // setup of first step: given a, b, x - return [y, of] (in that order)
    fn g_first_step_setup<CS: ConstraintSystem<E>>(&self, a: &Reg<E>, b: &Reg<E>)


    

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
        //println!("a val1: {}", a.full.1.get_value().unwrap());

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
        //println!("d val1: {}", self.get_full(cs, d)?.get_value().unwrap());

        // v[c] := (v[c] + v[d]) mod 2**w
        *c = self.add2(cs, c, d)?.into();
        //println!("c val1: {}", self.get_full(cs, c)?.get_value().unwrap());
        
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
        //println!("b val1: {}", self.get_full(cs, b)?.get_value().unwrap());

        // v[a] := (v[a] + v[b] + y) mod 2**w
        //println!("t1: {}", self.get_full(cs, &mut t1)?.get_value().unwrap());
        *a = self.add3(cs, a, b, &mut t1)?.into();
        //println!("a val2: {}", self.get_full(cs, a)?.get_value().unwrap());
        
        
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
        //println!("d val2: {}", self.get_full(cs, d)?.get_value().unwrap());
        
        // v[c] := (v[c] + v[d]) mod 2**w
        *c = self.add2(cs, c, d)?.into();
        //println!("c val2: {}", self.get_full(cs, c)?.get_value().unwrap());
        

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
        //println!("b val2: {}", self.get_full(cs, b)?.get_value().unwrap());

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

        for i in 0..16 {
            println!("regs: {}", self.get_full(cs, &mut v.regs[i])?.get_value().unwrap());
        }
      
        // Cryptographic mixing: ten rounds
        for i in 0..10 {
            // Message word selection permutation for this round.
            let s = &self.sigmas[i];

            self.G(cs, &mut v, 0, 4, 8, 12, &m[s[0]], &m[s[1]])?;
            //println!("olo");
            self.G(cs, &mut v, 1, 5, 9, 13, &m[s[2]], &m[s[3]])?;
            //println!("olot");
            self.G(cs, &mut v, 2, 6, 10, 14, &m[s[4]], &m[s[5]])?;
            //println!("olot1");
            self.G(cs, &mut v, 3, 7, 11, 15, &m[s[6]], &m[s[7]])?;
            //println!("olot2");
            self.G(cs, &mut v, 0, 5, 10, 15, &m[s[8]], &m[s[9]])?;
            //println!("olot3");
            self.G(cs, &mut v, 1, 6, 11, 12, &m[s[10]], &m[s[11]])?;
            //println!("olot4");
            self.G(cs, &mut v, 2, 7, 8, 13, &m[s[12]], &m[s[13]])?;
            //println!("olot5");
            self.G(cs, &mut v, 3, 4, 9, 14, &m[s[14]], &m[s[15]])?;
            //println!("olot6");
        }
        //println!("olotr");

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
            if i == 0 {
                hash_state.regs.push(self.twisted_iv_0.clone()); 
            }
            else {
                hash_state.regs.push(self.iv[i].clone());
            }
        }

        for (_is_first, is_last, block) in data.chunks(16).identify_first_last() 
        {
            assert_eq!(block.len(), 16);
            //println!("is last: {}", is_last);
            total_len += 64;
            hash_state = self.F(cs, hash_state, &block[..], total_len, is_last)?;
        }

        let mut res = Vec::with_capacity(8);
        for i in 0..8 {
            res.push(self.get_full(cs, &mut hash_state.regs[i])?);
        }

        for i in 0..8 {
            println!("res: {}", res[i].get_value().unwrap());
        }

        Ok(res)
    }
}
