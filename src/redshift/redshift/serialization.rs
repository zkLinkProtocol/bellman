use super::data_structures::*;
use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};
use crate::redshift::IOP::oracle::*;
use crate::redshift::IOP::oracle::coset_combining_rescue_tree::CosetCombinedQuery as RescueQuery;
use crate::redshift::IOP::oracle::coset_combining_blake2s_tree::CosetCombinedQuery as BlakeQuery;
use crate::redshift::IOP::FRI::coset_combining_fri::*;

// For now I use simple vector for serialization
// TODO: implement with serde


// TODO: better replace by tag = ENUM
pub type Label = &'static str;

pub type OracleHeight = usize;
pub type CosetSize = usize;

pub trait ToStream<F: PrimeField, SPP> : Sized {
    fn to_stream(self, container: &mut Vec<F>, params : SPP);
}

pub fn find_by_label<X: Clone>(label: Label, arr: &Vec<(Label, X)>) -> X {
    arr.iter().find(|elem| elem.0 == label).map(|elem| elem.1.clone()).expect("should contain")
}

impl<F: PrimeField> ToStream<F, ()> for F
{
    fn to_stream(self, container: &mut Vec<F>, _params : ())
    {
        container.push(self);
    } 
}

impl<F: PrimeField> ToStream<F, (usize)> for Vec<F> {
    fn to_stream(self, container: &mut Vec<F>, params : usize)
    {
        assert_eq!(self.len(), params);
        container.extend(self.into_iter());
    }
}

impl<F: PrimeField> ToStream<F, (usize)> for &[F] {
    fn to_stream(self, container: &mut Vec<F>, params : usize)
    {
        assert_eq!(self.len(), params);
        container.extend(self.into_iter());
    }
}

impl<F: PrimeField, I: Oracle<F, Commitment = F>> ToStream<F, OracleHeight> for SinglePolySetupData<F, I>
{
    fn to_stream(self, container: &mut Vec<F>, _params : OracleHeight)
    {
        container.push(self.setup_value);
        container.push(self.oracle.get_commitment());
    }
}
   
impl<F: PrimeField> ToStream<F, (CosetSize, OracleHeight)> for RescueQuery<F>
{
    fn to_stream(self, container: &mut Vec<F>, params : (CosetSize, OracleHeight))
    {
        self.values().to_stream(container, params.0);
        self.path.to_stream(container, params.1);
    }
}

impl<F: PrimeField> ToStream<F, (CosetSize, OracleHeight)> for BlakeQuery<F>
{
    fn to_stream(self, _container: &mut Vec<F>, _params : (CosetSize, OracleHeight))
    {
        unimplemented!();
    }
}

impl<F: PrimeField, I: Oracle<F, Commitment = F>> ToStream<F, OracleHeight> for RedshiftSetupPrecomputation<F, I> 
{
    fn to_stream(self, container: &mut Vec<F>, params : OracleHeight)
    {
        self.q_l_aux.setup_point.to_stream(container, ());

         // q_l, q_r, q_o, q_m, q_c, q_add_sel, s_id, sigma_1, sigma_2, sigma_3
        self.q_l_aux.to_stream(container, params);
        self.q_r_aux.to_stream(container, params);
        self.q_o_aux.to_stream(container, params);
        self.q_m_aux.to_stream(container, params);
        self.q_c_aux.to_stream(container, params);
        self.q_add_sel_aux.to_stream(container, params);
        self.s_id_aux.to_stream(container, params);
        self.sigma_1_aux.to_stream(container, params);
        self.sigma_2_aux.to_stream(container, params);
        self.sigma_3_aux.to_stream(container, params);
    }
}

impl<F: PrimeField, I: Oracle<F, Commitment = F>> ToStream<F, FriParams> for FriProof<F, I>
where I::Query : ToStream<F, (CosetSize, OracleHeight)>
{
    fn to_stream(self, container: &mut Vec<F>, fri_params: FriParams)
    {
        let coset_size = 1 << fri_params.collapsing_factor;
        let top_level_oracle_size = (fri_params.initial_degree_plus_one.get() * fri_params.lde_factor) / coset_size;
        let top_leve_height = log2_floor(top_level_oracle_size);
        let final_degree_plus_one = fri_params.final_degree_plus_one.get();
        
        let mut num_of_iters = log2_floor(fri_params.initial_degree_plus_one.get() / final_degree_plus_one) / fri_params.collapsing_factor;
        // we do not count the very first and the last iterations
        num_of_iters -= 1;
       
        self.commitments.to_stream(container, num_of_iters as usize);
        self.final_coefficients.to_stream(container, final_degree_plus_one);

        let labels = ["q_l", "q_r", "q_o", "q_m", "q_c", "q_add_sel", "s_id", "sigma_1", "sigma_2", "sigma_3",
            "a", "b", "c", "z_1", "z_2", "t_low", "t_mid", "t_high"];

        assert_eq!(self.upper_layer_queries.len(), fri_params.R);
        assert_eq!(self.queries.len(), fri_params.R);

        for (upper_level_query_list, intermidiate_queries) in self.upper_layer_queries.into_iter().zip(self.queries.into_iter()) 
        {
            for label in labels.iter() {
                let query = find_by_label(label, &upper_level_query_list);
                query.to_stream(container, (coset_size, top_leve_height as usize));
            }

            let mut cur_height = top_leve_height - fri_params.collapsing_factor;
            assert_eq!(intermidiate_queries.len(), num_of_iters as usize);

            for query in intermidiate_queries.into_iter() {
                query.to_stream(container, (coset_size, cur_height as usize));
                cur_height -= fri_params.collapsing_factor;
            }
        }
    }
}

impl<F: PrimeField, I: Oracle<F, Commitment = F>> ToStream<F, FriParams> for RedshiftProof<F, I>
where I::Query : ToStream<F, (CosetSize, OracleHeight)>
{
    fn to_stream(self, container: &mut Vec<F>, fri_params: FriParams)
    {          
        // containes opening values for:
        // a, b, c, c_shifted, q_l, q_r, q_o, q_m, q_c, q_add_sel, 
        // s_id, sigma_1, sigma_2, sigma_3, z_1, z_2, z_1_shifted, z_2_shifted, t_low, t_mid, t_high
        
        self.a_opening_value.to_stream(container, ());
        self.b_opening_value.to_stream(container, ());
        self.c_opening_value.to_stream(container, ());
        self.c_shifted_opening_value.to_stream(container, ());
        self.q_l_opening_value.to_stream(container, ());
        self.q_r_opening_value.to_stream(container, ());
        self.q_o_opening_value.to_stream(container, ());
        self.q_m_opening_value.to_stream(container, ());
        self.q_c_opening_value.to_stream(container, ());
        self.q_add_sel_opening_value.to_stream(container, ());
        self.s_id_opening_value.to_stream(container, ());
        self.sigma_1_opening_value.to_stream(container, ());
        self.sigma_2_opening_value.to_stream(container, ());
        self.sigma_3_opening_value.to_stream(container, ());
        self.z_1_opening_value.to_stream(container, ());
        self.z_2_opening_value.to_stream(container, ());
        self.z_1_shifted_opening_value.to_stream(container, ());
        self.z_2_shifted_opening_value.to_stream(container, ());
        self.t_low_opening_value.to_stream(container, ());
        self.t_mid_opening_value.to_stream(container, ());
        self.t_high_opening_value.to_stream(container, ());

        // contains commitments for a, b, c, z_1, z_2, t_low, t_mid, t_high
        let labels = ["a", "b", "c", "z_1", "z_2", "t_low", "t_mid", "t_high"];
        for label in labels.iter() {
            let commitment = find_by_label(label, &self.commitments);
            commitment.to_stream(container, ());
        }

        self.batched_FRI_proof.to_stream(container, fri_params);
    }
}