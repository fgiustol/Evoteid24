from zkjcj import * 
from itertools import groupby
import random

#set to True for enable verifications
ballot_validation = False
designated_verification = False 
cleansing_verification = False
tallying_verification = False


#number of candidates (should be 2 or more)
candidates = 2 

#number of voters (should be 2 or more)
voters = 10 

#total number of ballots 
total_ballots = voters * voters #on average each voter list has a number of ballot that is equal to the number of voters

vBB = [
        #voter_id, #pseudonym (0 wrong, 1 correct), #candidate 
        (random.randint(0, voters-1), random.randint(0,1), random.randint(0, candidates)) for _ in range(total_ballots)
]




print("--------------------")
print("Candidates:", candidates, "Voters:", voters, "Ballots: ", total_ballots)
vote_array = [-1]*voters
counter = 0

for bb_index in range(len(vBB) - 1, -1, -1):
    if counter == voters:
        break
    
    _, status, vote_c = vBB[bb_index]

    if status == 1 and vote_array[_] == -1:
        vote_array[_] = vote_c
        counter += 1

for i, vote_c in enumerate(vote_array):
    print(f"Voter {i} voted for {vote_c}")

#SETUP
g, order, pk_T, sk_T = setup()


sk_R = order.random()
pk_R = sk_R * g


#REGISTRATION

#Generating pseudonyms for each voter
sigma = [order.random() for i in range(voters)]

ct_hat = []
r = []
for i in range(voters):
    r.append(order.random())
    ct_hat.append(enc(g, pk_T, sigma[i], r[-1]))

#Generation of voter keys for designated verifier proofs
sk_V = [order.random() for i in range(voters)]
pk_V = [sk_V[i]*g for i in range(voters)]

#designated verifier proof for all voters
for i in range(voters):
    r_i = Secret(value=r[i])
    sigma_i = Secret(value=sigma[i])
    skR = Secret(value=sk_R)
    a = Secret()
    b = Secret()
    c = Secret()
    d = Secret()
    e = Secret()

    #PROOF OF ENCRYPTION   ct_hat[i] = Enc(pk_T, sigma[i], r) 
    DV_enc_stmt1 = DLRep(ct_hat[i][0], r_i*g) 
    DV_enc_stmt2 = DLRep(ct_hat[i][1], sigma_i*g + r_i*pk_T)
    
    #PROOF OF KNOWLEDGE pk_R=g*sk_R
    DV_know_stmt_R = DLRep(pk_R, skR  * g)
    
    #PROOF OF KNOWLEDGE (simulated) sk_V[i]=g*sk_V[i]
    DV_know_stmt_V = DLRep(pk_V[i], a * g)

    DV_stmt = (DV_enc_stmt1 & DV_enc_stmt2 &  DV_know_stmt_R)  | DV_know_stmt_V
    DV_stmt.subproofs[1].set_simulated()
    DV_nizk = DV_stmt.prove({sigma_i: sigma_i.value , r_i: r_i.value, skR: skR.value})


if designated_verification == True:
        #verification of designated verifier proofs
        DV_stmt_v = ( DLRep(ct_hat[i][0], b*g) & DLRep(ct_hat[i][1], c*g + b*pk_T) & DLRep(pk_R, d* g) ) | DLRep(pk_V[i], e * g)
        if DV_stmt_v.verify(DV_nizk) == False :
            print(f"\n\033[91m Designated verifer for voter {i} failed\033[0m")
else : print(f"\n\033[91m Skipping designated verifier proofs verifications\033[0m")  





#Init for avg time computation
e_time_obf = []
e_time_vote = []



#VOTING
print("\nSimulating voting...")

BB = []

for index, (voter_id,credential,vote_c)  in enumerate(vBB):
    #wrong credential   
    if  credential==0:
        s_time_obf = time.process_time_ns()
        BB.append(vote(g, order, ct_hat[voter_id], order.random(), vote_c,  pk_T, candidates))
        e_time_obf.append(time.process_time_ns() - s_time_obf)
    #correct credential    
    else: 
        s_time_vote = time.process_time_ns()
        BB.append(vote(g, order, ct_hat[voter_id], sigma[voter_id], vote_c,  pk_T, candidates))
        e_time_vote.append(time.process_time_ns() - s_time_vote)


#BALLOTS VALIDATION
if ballot_validation == True:
    failed = False
    s_time_verify = time.process_time_ns()
    for index in range(len(BB)):
        stmt_c = stmt((g, pk_T, BB[index][1], BB[index][0], BB[index][2]), (Secret(), Secret(), Secret()), candidates)
        if not stmt_c.verify(BB[index][3],repr(BB[index][1])):
            print(f"\n\033[91m Verification failed for index {index}, {vBB[index]}  \033[0m") 
            failed = True 
    e_time_verify = time.process_time_ns() - s_time_verify
    if not failed: print("\n\033[92m Verification successful for all ballots in the BB \033[0m")

else:  print("\n\033[91m Skipping verification for all ballots in the BB \033[0m")
    

#TALLYING

print("\nTallying...")
s_time_tally = time.process_time_ns()

#Cleansing 

# Creating a dictionary with ct_hat as key
L_ct_hat = []  
for _ in range(voters):
    L_ct_hat.append([])  
for ballot in BB:
    L_ct_hat[ct_hat.index(ballot[2])].append(ballot)        


#initialize L_ct_hat_Ti with (ct_hat, ct_0, 0)
ct_0 = [enc(g, pk_T, 0, 0) for _ in range(candidates)]
L_ct_hat_T = [[(ct_0, 0, ct_hatt)]  for ct_hatt in ct_hat]


for index, L_ct_hat_i  in enumerate(L_ct_hat):
    for ct_v, ct_sigma,_ ,_ in L_ct_hat_i:
        L_ct_hat_T[index].append(noise(g, order, sk_T, ct_v, ct_sigma, ct_hat[index], index, L_ct_hat, L_ct_hat_T[index], pk_T, candidates))      

#tally on the last ballots    
last_ballots = [L_ct_hat_Ti[-1][0] for L_ct_hat_Ti in L_ct_hat_T]
votes, nizk=tally(g,order,sk_T, last_ballots,candidates,voters)
e_time_tally = time.process_time_ns() - s_time_tally

#CLEANSING  verification
if cleansing_verification == True:
    failed = False
    
    for index, L_ct_hat_i  in enumerate(L_ct_hat):
        s_time_verify_filter = time.process_time_ns()
        Ti_index = 1 #skip the check of the initial ballot
        for ct_v, ct_sigma,_ ,_ in L_ct_hat_i:
            stmt_f = stmt_filter((g, pk_T, L_ct_hat, L_ct_hat_T[index][:Ti_index], ct_v, ct_sigma, ct_hat[index], L_ct_hat_T[index][Ti_index][0]), (Secret(), Secret()), candidates)
            if not stmt_f.verify(L_ct_hat_T[index][Ti_index][1]):
                print(f"\n\033[91m Verification failed for L_ct_hat_T{index}, index {Ti_index} \033[0m") 
                failed = True 
            Ti_index+=1
        e_time_verify_filter = time.process_time_ns() - s_time_verify_filter
    if not failed: print("\n\033[92m Verification successful for all ballots in the L_ct_hat_T \033[0m")

else:  print("\n\033[91m Skipping verification for all ballots in the L_ct_hat_T \033[0m")


#Tally verification
if tallying_verification==True:

    s_time_tally_verification = time.process_time_ns()
    stmt=[]
    for i in range(candidates):
            c0, c1 =(0*g), (0*g)
            for j in range(voters):
                c0+=last_ballots[j][i][0]
                c1+=last_ballots[j][i][1]
            stmt.append(stmt_tally(g, order, votes[i],c0, c1, Secret()))
    
    for i in range(candidates):
        print(f"Verification for tallying of votes for candidate {i+1}: {stmt[i].verify(nizk[i])}")
    e_time_tally_verification = time.process_time_ns() - s_time_tally_verification
else : print("\n\033[91m Skipping tally verification \033[0m")

#TIMINGS

print(f"\nTimings")
print("=======")
print("Ballot obfuscation time (avg):", round(sum(e_time_obf)/len(e_time_obf)/1000000,3), "ms")
print("Ballot vote time (avg):", round(sum(e_time_vote)/len(e_time_vote)/1000000,3), "ms")
if ballot_validation == True: print("BB verification time:", e_time_verify/1000000, "ms")
print("Tallying time:", e_time_tally/1000000, "ms")
if cleansing_verification == True: print("Cleansing verification time:", e_time_verify_filter/1000000, "ms")
if tallying_verification == True: print("Tallying verification time:", e_time_tally_verification/1000000, "ms")
print("=======")


