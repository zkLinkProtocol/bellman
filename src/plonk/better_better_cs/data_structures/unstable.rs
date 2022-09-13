use crate::pairing::ff::*;
use crate::pairing::*;
use crate::plonk::polynomials::*;
use super::cs::GateInternal;
use std::alloc::{Allocator, Global};

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum PolyIdentifier {
    VariablesPolynomial(usize),
    WitnessPolynomial(usize),
    GateSetupPolynomial(&'static str, usize),
    GateSelector(&'static str),
    LookupSelector,
    LookupTableEntriesPolynomial(usize),
    NamedSetupPolynomial(&'static str),
    PermutationPolynomial(usize),
}

pub const LOOKUP_TABLE_TYPE_POLYNOMIAL: &'static str = "LOOKUP_TABLE_TYPE_POLYNOMIAL";

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct TimeDilation(pub usize);
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct PolynomialInConstraint(pub PolyIdentifier, pub TimeDilation);

impl PolynomialInConstraint{
    pub const fn from_id(id: PolyIdentifier) -> Self {
        Self(id, TimeDilation(0))
    }
    pub const fn from_id_and_dilation(id: PolyIdentifier, dilation: usize) -> Self {
        Self(id, TimeDilation(dilation))
    }
    pub const fn into_id_and_raw_dilation(self) -> (PolyIdentifier, usize) {
        (self.0, (self.1).0)
    }
}

pub enum PolynomialProxy<'a, 
    F: PrimeField, 
    P: PolynomialForm, 
    A: Allocator + Clone = Global
> {
    Borrowed(&'a Polynomial<F, P, A>),
    Owned(Polynomial<F, P, A>),
}

impl<'a, 
    F: PrimeField, 
    P: PolynomialForm, 
    A: Allocator + Clone,
> PolynomialProxy<'a, F, P, A> {
    pub fn from_owned(poly: Polynomial<F, P, A>) -> Self {
        PolynomialProxy::Owned(poly)
    }

    pub fn from_borrowed(poly: &'a Polynomial<F, P, A>) -> Self {
        PolynomialProxy::Borrowed(poly)
    }

    pub fn as_ref(&self) -> &Polynomial<F, P, A> {
        match self {
            PolynomialProxy::Borrowed(b) => {
                &*b
            },
            PolynomialProxy::Owned(o) => {
                &o
            }
        }
    }

    pub fn as_data_ref(&self) -> &[F] {
        match self {
            PolynomialProxy::Borrowed(b) => {
                b.as_ref()
            },
            PolynomialProxy::Owned(o) => {
                o.as_ref()
            }
        }
    }

    pub fn as_data_ref_mut(&mut self) -> &mut [F] {
        match self {
            PolynomialProxy::Borrowed(..) => {
                unreachable!("Can not borrow mutable for non-owned proxy")
            },
            PolynomialProxy::Owned(o) => {
                o.as_mut()
            }
        }
    }

    pub fn into_poly(self) -> Polynomial<F, P, A> {
        match self {
            PolynomialProxy::Borrowed(b) => {
                b.clone()
            },
            PolynomialProxy::Owned(o) => {
                o
            }
        }
    }

    pub fn clone_as_owned(&self) -> Self {
        match self {
            PolynomialProxy::Borrowed(ref b) => {
                PolynomialProxy::Owned((*b).clone())
            },
            PolynomialProxy::Owned(o) => {
                PolynomialProxy::Owned(o.clone())
            }
        }
    }
}

pub fn clone_as_borrowed<'a, 'b: 'a, F: PrimeField, P: PolynomialForm, A: Allocator + Clone>(
    src: &'a PolynomialProxy<'b, F, P, A>
) -> PolynomialProxy<'a, F, P, A> {
    match src {
        PolynomialProxy::Borrowed(ref b) => {
            PolynomialProxy::Borrowed(*b)
        },
        PolynomialProxy::Owned(ref o) => {
            PolynomialProxy::Borrowed(o)
        }
    }
}

// impl<'a, F: PrimeField, P: PolynomialForm> Clone for PolynomialProxy<'a, F, P> {
//     fn clone(&self) -> Self {
//         match self {
//             PolynomialProxy::Borrowed(ref b) => {
//                 PolynomialProxy::Borrowed(b)
//             },
//             PolynomialProxy::Owned(ref o) => {
//                 PolynomialProxy::Borrowed(o)
//             }
//         }
//     }
// }


pub struct AssembledPolynomialStorage<'a, E: Engine, A: Allocator + Clone = Global> {
    pub state_map: std::collections::HashMap<PolyIdentifier, PolynomialProxy<'a, E::Fr, Values, A>>,
    pub witness_map: std::collections::HashMap<PolyIdentifier, PolynomialProxy<'a, E::Fr, Values, A>>,
    pub setup_map: std::collections::HashMap<PolyIdentifier, PolynomialProxy<'a, E::Fr, Values, A>>,
    pub scratch_space: std::collections::HashMap<PolynomialInConstraint, PolynomialProxy<'a, E::Fr, Values, A>>,
    pub gate_selectors: std::collections::HashMap<PolyIdentifier, PolynomialProxy<'a, E::Fr, Values, A>>,
    pub named_polys: std::collections::HashMap<PolyIdentifier, PolynomialProxy<'a, E::Fr, Values, A>>,
    pub is_bitreversed: bool,
    pub lde_factor: usize
}

pub struct AssembledPolynomialStorageForMonomialForms<'a, E: Engine, A: Allocator + Clone = Global> {
    pub state_map: std::collections::HashMap<PolyIdentifier, PolynomialProxy<'a, E::Fr, Coefficients, A>>,
    pub witness_map: std::collections::HashMap<PolyIdentifier, PolynomialProxy<'a, E::Fr, Coefficients, A>>,
    pub setup_map: std::collections::HashMap<PolyIdentifier, PolynomialProxy<'a, E::Fr, Coefficients, A>>,
    pub gate_selectors: std::collections::HashMap<PolyIdentifier, PolynomialProxy<'a, E::Fr, Coefficients, A>>,
    pub named_polys: std::collections::HashMap<PolyIdentifier, PolynomialProxy<'a, E::Fr, Coefficients, A>>,
}

impl<'a, E: Engine, A: Allocator + Clone> AssembledPolynomialStorage<'a, E, A> {
    pub fn get_poly(&self, id: PolyIdentifier) -> &Polynomial<E::Fr, Values, A> {
        match id {
            p @ PolyIdentifier::VariablesPolynomial(..) => {
                self.state_map.get(&p).expect(&format!("poly {:?} must exist", p)).as_ref()
            },
            p @ PolyIdentifier::WitnessPolynomial(..) => {
                self.witness_map.get(&p).expect(&format!("poly {:?} must exist", p)).as_ref()
            },
            p @ PolyIdentifier::GateSetupPolynomial(..) => {
                self.setup_map.get(&p).expect(&format!("poly {:?} must exist", p)).as_ref()
            },
            p @ PolyIdentifier::GateSelector(..) => {
                self.gate_selectors.get(&p).expect(&format!("poly {:?} must exist", p)).as_ref()
            },
            p @ PolyIdentifier::PermutationPolynomial(..) => {
                self.setup_map.get(&p).expect(&format!("poly {:?} must exist", p)).as_ref()
            },
            p @ PolyIdentifier::LookupSelector => {
                self.named_polys.get(&p).expect(&format!("poly {:?} must exist", p)).as_ref()
            },
            p @ PolyIdentifier::LookupTableEntriesPolynomial(..) => {
                self.named_polys.get(&p).expect(&format!("poly {:?} must exist", p)).as_ref()
            },
            p @ PolyIdentifier::NamedSetupPolynomial(..) => {
                self.named_polys.get(&p).expect(&format!("poly {:?} must exist", p)).as_ref()
            },
            _ => {
                unreachable!()
            }
        }
    }
    pub fn get_poly_at_step(&self, id: PolyIdentifier, step: usize) -> E::Fr {
        assert!(self.is_bitreversed == false);
        assert!(self.lde_factor == 1);
        let p = self.get_poly(id);
        p.as_ref()[step]
    }

    pub fn get_selector_for_gate(&self, gate: &dyn GateInternal<E>) -> &Polynomial<E::Fr, Values, A> {
        let gate_name = gate.name();
        let p = PolyIdentifier::GateSelector(gate_name);
        self.gate_selectors.get(&p).expect(&format!("poly {:?} must exist", p)).as_ref()
    }

    pub fn new(bitreversed: bool, lde_factor: usize) -> Self {
        Self {
            state_map: std::collections::HashMap::new(),
            witness_map: std::collections::HashMap::new(),
            setup_map: std::collections::HashMap::new(),
            gate_selectors: std::collections::HashMap::new(),
            scratch_space: std::collections::HashMap::new(),
            named_polys: std::collections::HashMap::new(),
            is_bitreversed: bitreversed,
            lde_factor
        }
    }

    pub fn add_setup_polys<'b: 'a>(&mut self, ids: &[PolyIdentifier], polys: &'b [Polynomial<E::Fr, Values, A>]) {
        assert_eq!(ids.len(), polys.len());
        for (id, poly) in ids.iter().zip(polys.iter()) {
            let proxy = PolynomialProxy::from_borrowed(poly);

            match id {
                p @ PolyIdentifier::GateSetupPolynomial(..) => {
                    self.setup_map.insert(p.clone(), proxy);
                },
                p @ PolyIdentifier::GateSelector(..) => {
                    self.setup_map.insert(p.clone(), proxy);
                },
                p @ PolyIdentifier::PermutationPolynomial(..) => {
                    self.setup_map.insert(p.clone(), proxy);
                },
                p @ PolyIdentifier::LookupSelector => {
                    self.named_polys.insert(p.clone(), proxy);
                },
                p @ PolyIdentifier::LookupTableEntriesPolynomial(..) => {
                    self.named_polys.insert(p.clone(), proxy);
                },
                p @ PolyIdentifier::NamedSetupPolynomial(..) => {
                    self.named_polys.insert(p.clone(), proxy);
                },
                _ => {
                    unreachable!()
                }
            }
        }
    }
}

impl<'a, E: Engine, A: Allocator + Clone> AssembledPolynomialStorageForMonomialForms<'a, E, A> {
    pub fn get_poly(&self, id: PolyIdentifier) -> &Polynomial<E::Fr, Coefficients, A> {
        match id {
            p @ PolyIdentifier::VariablesPolynomial(..) => {
                self.state_map.get(&p).expect(&format!("poly {:?} must exist", p)).as_ref()
            },
            p @ PolyIdentifier::WitnessPolynomial(..) => {
                self.witness_map.get(&p).expect(&format!("poly {:?} must exist", p)).as_ref()
            },
            p @ PolyIdentifier::GateSetupPolynomial(..) => {
                self.setup_map.get(&p).expect(&format!("poly {:?} must exist", p)).as_ref()
            },
            p @ PolyIdentifier::GateSelector(..) => {
                self.gate_selectors.get(&p).expect(&format!("poly {:?} must exist", p)).as_ref()
            },
            p @ PolyIdentifier::PermutationPolynomial(..) => {
                self.setup_map.get(&p).expect(&format!("poly {:?} must exist", p)).as_ref()
            },
            p @ PolyIdentifier::LookupSelector => {
                self.named_polys.get(&p).expect(&format!("poly {:?} must exist", p)).as_ref()
            },
            p @ PolyIdentifier::LookupTableEntriesPolynomial(..) => {
                self.named_polys.get(&p).expect(&format!("poly {:?} must exist", p)).as_ref()
            },
            p @ PolyIdentifier::NamedSetupPolynomial(..) => {
                self.named_polys.get(&p).expect(&format!("poly {:?} must exist", p)).as_ref()
            },
        }
    }

    pub fn new() -> Self {
        Self {
            state_map: std::collections::HashMap::new(),
            witness_map: std::collections::HashMap::new(),
            setup_map: std::collections::HashMap::new(),
            gate_selectors: std::collections::HashMap::new(),
            named_polys: std::collections::HashMap::new(),
        }
    }

    pub fn get_selector_for_gate(&self, gate: &dyn GateInternal<E>) -> &Polynomial<E::Fr, Coefficients, A> {
        let gate_name = gate.name();
        let p = PolyIdentifier::GateSelector(gate_name);
        self.state_map.get(&p).expect(&format!("poly {:?} must exist", p)).as_ref()
    }

    pub fn add_setup_polys<'b: 'a>(&mut self, ids: &[PolyIdentifier], polys: &'b [Polynomial<E::Fr, Coefficients, A>]) {
        assert_eq!(ids.len(), polys.len());
        for (id, poly) in ids.iter().zip(polys.iter()) {
            let proxy = PolynomialProxy::from_borrowed(poly);

            match id {
                p @ PolyIdentifier::GateSetupPolynomial(..) => {
                    self.setup_map.insert(p.clone(), proxy);
                },
                p @ PolyIdentifier::GateSelector(..) => {
                    self.setup_map.insert(p.clone(), proxy);
                },
                p @ PolyIdentifier::PermutationPolynomial(..) => {
                    self.setup_map.insert(p.clone(), proxy);
                },
                p @ PolyIdentifier::LookupSelector => {
                    self.named_polys.insert(p.clone(), proxy);
                },
                p @ PolyIdentifier::LookupTableEntriesPolynomial(..) => {
                    self.named_polys.insert(p.clone(), proxy);
                },
                p @ PolyIdentifier::NamedSetupPolynomial(..) => {
                    self.named_polys.insert(p.clone(), proxy);
                }
                _ => {
                    unreachable!()
                }
            }
        }
    }
}

pub struct LookupDataHolder<'a, E: Engine, A: Allocator + Clone = Global> {
    pub eta: E::Fr,
    pub f_poly_unpadded_values: Option<Polynomial<E::Fr, Values, A>>,
    pub t_poly_unpadded_values: Option<PolynomialProxy<'a, E::Fr, Values, A>>,
    pub t_shifted_unpadded_values: Option<PolynomialProxy<'a, E::Fr, Values, A>>,
    pub s_poly_unpadded_values: Option<Polynomial<E::Fr, Values, A>>,
    pub s_shifted_unpadded_values: Option<Polynomial<E::Fr, Values, A>>,
    pub t_poly_monomial: Option<PolynomialProxy<'a, E::Fr, Coefficients, A>>,
    pub s_poly_monomial: Option<Polynomial<E::Fr, Coefficients, A>>,
    pub selector_poly_monomial: Option<PolynomialProxy<'a, E::Fr, Coefficients, A>>,
    pub table_type_poly_monomial: Option<PolynomialProxy<'a, E::Fr, Coefficients, A>>,
}