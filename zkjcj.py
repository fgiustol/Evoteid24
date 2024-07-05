from zksk import Secret, DLRep
from zksk.primitives.dl_notequal import DLNotEqual
from zksk.primitives.rangeproof import RangeStmt, RangeOnlyStmt, PowerTwoRangeStmt
import petlib.bn as bn
from elGamal import keygen, dec, enc, re_enc
import time
from functools import reduce

def setup():
    #Generation of public params and Tallier key pair
    g, order, pk_T, sk_T = keygen()
    
    #Generation of Tallier key pair
    return g, order, pk_T, sk_T

def stmt_filter(public_params, private_params, candidates):
    """Constructs the statement for the ZK proofs in noise 

    Args: 
        public_params (tuple): public parameters
        private_params (tuple): private parameters
        candidate (int): the number of candidates

    Returns:
        full_stmt (tuple): the statement for the ZK proofs in noise 
    
    """
    g, pk_T, L_ct_hat, L_ct_hat_Ti, ct_v, ct_sigma, ct_hat, ct_v_renc  = public_params
    r_t, sk_T = private_params


    #compute ct_sigma-ct_hat
    c0, c1 = ct_sigma[0] - ct_hat[0], ct_sigma[1] - ct_hat[1]

    #tricks to make the zksk library happy
    one = Secret(value=1)
    neg_c0 = (-1)*c0

    #----------
    #RELATION eq 
    #----------
    
    #PROOF OF RE-ENCRYPTION ct_value = ReEnc(pk_T, ct_v, r_t)
    R_eq_reenc_stmt = [0]*candidates
    for i in range(candidates):
        R_eq_reenc_stmt[i] = DLRep(ct_v_renc[i][0], one*ct_v[i][0] + r_t*g) & DLRep(ct_v_renc[i][1], one*ct_v[i][1] + r_t*pk_T)
    R_eq_result_stmt = reduce(lambda x, y: x & y, R_eq_reenc_stmt)

    #PROOF OF DECRYPTION   1 = Dec(sk_T, ct_sigma-ct_hat)
    R_eq_dec_stmt = DLRep(0*g, one*c1 + sk_T*neg_c0)

    R_eq_stmt = R_eq_result_stmt & R_eq_dec_stmt


    #----------
    #RELATION uneq 
    #----------


    #PROOF OF RE-ENCRYPTION ct_value = ReEnc(pk_T, L_ct_hat_Ti[-1[0]], r_t)
    ct_x = L_ct_hat_Ti[-1][0]
    R_uneq_reenc_stmt = [0]*candidates
    for i in range(candidates):
        R_uneq_reenc_stmt[i] = DLRep(ct_v_renc[i][0], one*ct_x[i][0] + r_t*g) & DLRep(ct_v_renc[i][1], one*ct_x[i][1] + r_t*pk_T)
    R_uneq_result_stmt = reduce(lambda x, y: x & y, R_uneq_reenc_stmt)

    #PROOF OF DL INEQUALITY    1 <> Dec(sk_T, ct_sigma-ct_hat) 
    R_uneq_dec_stmt = DLNotEqual([pk_T,g],[c1,c0],sk_T)


    R_uneq_stmt = R_uneq_result_stmt & R_uneq_dec_stmt


    #RELATION T
    return R_eq_stmt | R_uneq_stmt





def stmt(public_params, private_params, candidates):
    """Constructs the statement for the ZK proofs in Vote 

    Args: 
        public_params (tuple): public parameters
        private_params (tuple): private parameters
        candidate (int): the number of candidates

    Returns:
        full_stmt (tuple): the statement for the ZK proofs in Vote 
    
    """
    g, pk_T, ct_sigma, ct_v, ct_hat  = public_params
    r_v, r_sigma, sec_sigma = private_params
    R_range_stmt0, R_range_stmt1, R_enc_stmt = [], [], [] 

    #----------
    #RELATION Beta
    #----------

    #PROOF OF VOTE ENCRYPTION  (correctness)
    #(i) proves that each encrypted vote is either 0 or 1
    for i in range(candidates):
        #encryption of 0
        R_range_stmt0.append(DLRep(ct_v[i][0], r_v*g) & DLRep(ct_v[i][1], r_v*pk_T))
        #encryption of 1
        R_range_stmt1.append(DLRep(ct_v[i][0], r_v*g) & DLRep(ct_v[i][1] - g, r_v*pk_T))

    #(ii) proves that the sum of all encrypted votes is either 0 or 1 
    elements_c0, elements_c1 = list(map(lambda x: x[0], ct_v)), list(map(lambda x: x[1], ct_v))
    product_c0, product_c1 = reduce(lambda x, y: x + y, elements_c0), reduce(lambda x, y: x + y, elements_c1)
    exp1, exp2= candidates*g, candidates*pk_T
    #encryption of 0
    R_enc_sum_stmt0 = DLRep(product_c0, exp1*r_v) & DLRep(product_c1, exp2*r_v)
    #encryption of 1
    R_enc_sum_stmt1 = DLRep(product_c0, exp1*r_v) & DLRep(product_c1 - g, exp2*r_v)

    #flattening of the or-proofs as required by the zksk library and making it also more efficient 
    #instead of proving (R_range_stmt0_c_0 | R_range_stmt_1_c_0) & ... & (R_range_stmt0_c_i | R_range_stmt_1_c_i) & (R_enc_sum_stm0 | R_enc_sum_stm0) 
    #we prove (R_range_stmt0_c_0 & ... & R_range_stmt0_c_i & R_enc_sum_stm0) |  ... | (R_range_stmt_c_1 & ... & R_range_stmt0_c_i & R_enc_sum_stmt1) ) 
    for i in range(candidates):
        if i==0:
            #statement for a vote for the first candidate (1 0 ...  0)  
            R_enc_stmt.append(R_enc_sum_stmt1 & R_range_stmt1[i] & reduce(lambda x, y: x & y, R_range_stmt0[i+1:]))
        elif i==candidates-1:
            #statement for a vote for the last candidate (0 0 ... 1) 
            R_enc_stmt.append(R_enc_sum_stmt1 & R_range_stmt1[i] & reduce(lambda x, y: x & y, R_range_stmt0[:i])) 
            #statement for a vote for any other candidate (0 ... 1 ... 0) 
        else: R_enc_stmt.append(R_enc_sum_stmt1 & R_range_stmt1[i] & reduce(lambda x, y: x & y, R_range_stmt0[:i]) & reduce(lambda x, y: x & y, R_range_stmt0[i+1:])) 
    #statement for a vote for abstention (0 0 ... 0) 
    R_enc_stmt.append(R_enc_sum_stmt0 & reduce(lambda x, y: x & y, R_range_stmt0[:])) 

    R_enc_stmt = reduce(lambda x, y: x | y, R_enc_stmt) 

    #PROOF OF ENCRYPTION   ct_sigma = Enc(pk_t, sigma, r_sigma) 
    R_enc_stmt2 = DLRep(ct_sigma[0], r_sigma*g) & DLRep(ct_sigma[1], sec_sigma*g + r_sigma*pk_T)

    #RELATION 1 STATEMENT
    return R_enc_stmt  & R_enc_stmt2 
   # & R_enc_stmt3




def vote(g, order, ct_hat,  sigma,  v, pk_T, candidates):
    """Casts a vote and constructs all sub-proofs and witnesses for R_beta  

    Args:
        g (EcPt): generator of the EC group
        order (Bn): order of the EC group
        sigma (Bn): secret pseudonym of the Voter
        pk_T (EcPt): public key of the Tallier
        v (int): vote value
        candidates (int): the number of candidates

    Returns:
        ballot: the encrypted vote and the NIZK proof

    
    """
    sec_sigma = Secret(value=sigma)
    
    vect_v = [0]*candidates
    for i in  range(candidates):
        vect_v[i] = Secret(value=0)
    if v>0:
        #generate vect_v based on the vote otherwise abstention
        vect_v[v-1] = Secret(value=1)

    #generating the new ballot
    r_v = Secret(value=order.random())
    r_sigma = Secret(value=order.random())
    ct_v = [enc(g, pk_T, vect_v[i].value, r_v.value) for i in range(candidates)]
    ct_sigma = enc(g, pk_T, sec_sigma.value, r_sigma.value)  

    full_stmt=stmt((g, pk_T, ct_sigma, ct_v, ct_hat), (r_v, r_sigma, sec_sigma), candidates)

    simulation_indexes=[]

    #if the vote is for abstention then we need to simulate the proof for all candidates
    simulation_indexes=[i for i in range(candidates)] if v==0 else [i for i in range(candidates+1) if i!=v-1]

    #setting the relations to be simulated
    for i in simulation_indexes:
        full_stmt.subproofs[0].subproofs[i].set_simulated()
    
    #constructing the witness for each candidate vote encryption 
    vect_v_str=[('vect_v'+str([i]), vect_v[i].value) for i in range(candidates)]
    sec_dict=dict(vect_v_str)

    #prove the statement
    nizk = full_stmt.prove(sec_dict.update({r_v: r_v.value, r_sigma: r_sigma.value, sec_sigma: sec_sigma.value}),repr(ct_sigma))

    return (ct_v, ct_sigma, ct_hat, nizk)
           
def noise(g, order, sk_T, ct_v, ct_sigma, ct_hat, index, L_ct_hat, L_ct_hat_Ti, pk_T, candidates):      
   """Cast a ballot noise and constructs all sub-proofs and witnesses for R_eq or R_uneq
    
    Args:
        g (EcPt): generator of the EC group
        order (Bn): order of the EC group
        sk_T (Bn): secret key of the tallier
        ct_v :
        ct_sigma :
        ct_hat :
        index (int): index of the current L_ct_hat_T element
        L_ct_hat (list): 
        L_ct_hat_Ti (list): 
        pk_T (EcPt): public key of tallier

    Returns:
        ballot: the encrypted vote and  the NIZK proof
   """
   r_t = Secret(value=order.random())
   sk = Secret(value=sk_T)
   
   if dec(ct_sigma, sk.value)==dec(ct_hat, sk.value): 
    #we re-randomize the ballot in the voter's L_ct_hat 
    ct_value = ct_v   
    sim_relation=1
   # print(f"[{len(cbr)}] correct pseudonym")
   else : 
       #we re-randomize the last ballot in item of L_ct_hat_Ti
       ct_value = L_ct_hat_Ti[-1][0]   
       sim_relation=0
       #print(f"\033[31m[{len(cbr)}] VS obfuscated previous last ballot\033[0m")
    
   ct_v_renc = [re_enc(g, pk_T, ct_value[i], r_t.value) for i in range(candidates)]


   full_stmt=stmt_filter((g, pk_T, L_ct_hat, L_ct_hat_Ti, ct_v, ct_sigma, ct_hat, ct_v_renc),(r_t,sk), candidates )
   
   #depending on whether dec(ct_sigma, sk.value)==dec(ct_hat, sk.value) or not we simulate R_eq or R_uneq
   full_stmt.subproofs[sim_relation].set_simulated()
   nizk = full_stmt.prove({r_t: r_t.value, sk: sk.value})

   return (ct_v_renc, nizk)
   

def stmt_tally(g, order, votes, c0, c1, sk_T):
    """Constructs the statement for the ZK proofs in Tally

    Args:
        g (EcPt): generator of the EC group
        order (Bn): order of the EC group
        votes (int): number of votes for a candidate
        c0 (EcPt): sum of all encrypted votes for a candidate
        c1 (EcPt): sum of all encrypted votes for a candidate
        sk_T (Bn): secret key of the Tallier

    Returns:
        full_stmt (tuple): the statement for the ZK proofs in Tally

    """
    one=Secret(value=1)
    neg_c0 = (-1)*c0
    return DLRep(votes*g, one*c1 + sk_T*neg_c0)

def tally(g, order, sk_T, ballots, candidates, voters):
    """Tally the votes and constructs all sub-proofs and witnesses for Tally
    
    Args:
        g (EcPt): generator of the EC group
        order (Bn): order of the EC group
        sk_T (Bn): secret key of the Tallier
        ballots (): the last ballots from all voter L_ct_hat_T 
        candidates (int): number of candidates
        voters (int): number of registered voters

    Returns:
        votes (list): the number of votes for each candidate
        nizk (list): the NIZK proofs for each candidate

    """
    sk=Secret(value=sk_T)
    stmt, nizk=[], []
    votes_for_candidate=[0]*candidates
    
    for i in range(candidates):
        c0, c1 =(0*g), (0*g)

        #summing up all encrypted votes for a candidate
        for j in range(voters):
            c0+=ballots[j][i][0]
            c1+=ballots[j][i][1]
        sum_votes=dec((c0,c1), sk_T)

        #finding the number of votes for a candidate
        for j in range(voters):
            if sum_votes==j*g:
                votes_for_candidate[i]=j
                break

        print("Votes for Candidate",i+1,":", votes_for_candidate[i])

        #constructing the statement for the ZK proof
        stmt.append(stmt_tally(g, order, j,c0, c1, sk))

        #proving the statement
        nizk.append(stmt[-1].prove({sk: sk.value}))

    print("Abstention votes:", voters-sum(votes_for_candidate)) 
    return votes_for_candidate, nizk


