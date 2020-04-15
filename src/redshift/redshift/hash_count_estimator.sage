# script for estimation the number of Hashes in Redshift Circuit

RESCUE_INPUT_SIZE = 2
RESCUE_OUTPUT_SIZE = 1

FRI_NUM_QUERIES = 80
FRI_LDE_FACTOR = 16

INITIAL_POLY_DEG = 2^24
FINAL_POLY_DEG = 16

# we locate all elements of the same coset in one leaf of the OracleTree
# if we enlarge the number of cosetsm there will be less intermidiate Fri Oracles and smaller Trees
# However, we can't obviously make coset size too large - it will affect security a lot
# "Safe" numbers are 2, 4, 8
COSET_SIZE = 4

# enum
RESCUE_STATE_ABSORBING = 0
RESCUE_STATE_SQUEEZING = 1

class Channel:
    
    def __init__(self):
        self.channel_hashes = 0
        self.cur_absorded = 0
        self.cur_squeezed = 0
        self.state = RESCUE_STATE_ABSORBING
    
    def absord(self, num_absorded_elems):
        if self.state == RESCUE_STATE_SQUEEZING:
            self.state = RESCUE_STATE_ABSORBING
            self.cur_absorded = 0
            
        self.cur_absorded += num_absorded_elems
        while self.cur_absorded > RESCUE_INPUT_SIZE:
            self.cur_absorded -= RESCUE_INPUT_SIZE
            self.channel_hashes += 1
            
    def squeeze(self, num_squeezed_elems):
        if self.state == RESCUE_STATE_ABSORBING:
            self.channel_hashes += 1
            self.state = RESCUE_STATE_SQUEEZING
            self.cur_squeezed = 0
        
        self.cur_squeezed += num_squeezed_elems
        while self.cur_squeezed > RESCUE_OUTPUT_SIZE:
            self.cur_squeezed -= RESCUE_OUTPUT_SIZE
            self.channel_hashes += 1
        
    def get_num_hashes(self):
        return self.channel_hashes
    
    def add_hashes_count(self, num_hashes):
        self.channel_hashes += num_hashes
        
    def set_state(self, state, num_elems):
        self.state = state
        if state == RESCUE_STATE_ABSORBING:
            self.cur_absorded = num_elems
        else:
            self.cur_squeezed = num_elems
        

def log2(n):
    # assert the number is positive and is power of 2
    n = Integer(n)
    assert(n > 0 and n & (n-1) == 0)
    
    pow = 0
    while (1 << (pow+1)) <= n:
        pow += 1;
    return pow
        

def estimate_hash_number():
    
    channel = Channel()
    
    # absord main witnesses: a, b, c
    channel.absord(3)
    # squeeze beta, gama
    channel.squeeze(2)
    # absord z_1, z_2
    channel.absord(2)
    # squeeze alpha
    channel.squeeze(1)
    # absord t_low, t_high, t_mid
    channel.absord(3)
    # squeeze evaluation point z and FRI upper layer aggregation challenge
    channel.squeeze(2)
    
    # now we need to generate fri_challenges - parameters used in FRI setup step
    # it is the coefficients c in f_odd(x) + cf_even(x) which connects two adjacent layers of FRI
    
    # the first "virtual" oracle is of the size lde_factor * initial_poly_len
    # each iteration the number of oracles is reduced by coset_size until we reach final_poly_len
    
    # fri challenges are generated in the following pattern:
    # channel.produce_field_element_challenge()
    # for step in num_intermidiate_oracles:
    #   channel.consume(&commitment);
    #   channel.produce_field_element_challenge()
    
    # we want to simplify this pattern and exploit the fact that RESCUE_NUM_INPUTS >= RESCUE_NUM_OUTPUTS >= 1
    
    num_intermidiate_oracles = log2(INITIAL_POLY_DEG / FINAL_POLY_DEG) / log2(COSET_SIZE) - 1
    channel.squeeze(1)
    channel.add_hashes_count(num_intermidiate_oracles)
    channel.set_state(RESCUE_STATE_SQUEEZING, 1)
    
    # generate top level indexed for FRI query phase:
    channel.squeeze(FRI_NUM_QUERIES)
      
    # we have calculated the number of all the channel (transcript) related 
    # let's find out the number of Merklee proof related hashes!
    oracle_hashes = 0
    
    # there are 20 top-level oracles of "virtual" size lde_factor * initial_poly_size,
    # [a, b, c, q_l, q_r, q_o, q_m, q_c, q_add_sel, s_id, sigma_1, sigma_2, sigma_3,
    # z_1, z_2, z_1_shifted, z_2_shifted, t_low, t_mid, t_high].len() = 20
    # there are (num_intermidiate) oracles: the first one is of size
    # I say "virtual" as there are COSET number of elements encoded into the same leaf, so that
    # "actual" top-level oracle size is k = lde_factor * initial_poly_size / COSET_SIZE
    # so the height of merklee proof (which is equal to the number of hashes) is log2(k)
    
    # the first intermidiate oracle height is log2(k) - log2(COSET_SIZE)
    # the second is of height log2(k) - 2 * log2(COSET_SIZE)
    # and so on
    
    # for each oracle (it doesn't matter either it is top-level or intermidiate)
    # we need to use COSET_SIZE hashes to hash all elements of the same coset (which belong to the same leaf)
    
    NUM_TOP_LEVEL_ORACLES = 20
    LOG_COSET_SIZE = log2(COSET_SIZE)
    TOP_LEVEL_TREE_HEIGHT = log2(FRI_LDE_FACTOR * INITIAL_POLY_DEG) - LOG_COSET_SIZE
    NUM_HASHES_PER_LEAF = COSET_SIZE
    
    top_level_hashes = (TOP_LEVEL_TREE_HEIGHT + NUM_HASHES_PER_LEAF) * NUM_TOP_LEVEL_ORACLES
    oracle_hashes += top_level_hashes
    
    cur_tree_height = TOP_LEVEL_TREE_HEIGHT - LOG_COSET_SIZE
    for _ in xrange(num_intermidiate_oracles):
        oracle_hashes += cur_tree_height + NUM_HASHES_PER_LEAF
        cur_tree_height -= LOG_COSET_SIZE
    
    # we repeate this query process FRI_NUM_QUERIES_TIMES!
    oracle_hashes *= FRI_NUM_QUERIES
    
    return (channel.get_num_hashes(), oracle_hashes)


channel_hashes, oracle_hashes = estimate_hash_number()

print "channel (transcript) hashes count: ", channel_hashes
print "Merklee proof hashes count: ", oracle_hashes
print "Total: ", channel_hashes + oracle_hashes
