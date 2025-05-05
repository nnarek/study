------------------------------ MODULE Session4_ex3 ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT int_set
ASSUME int_set \subseteq Int


(*********  

--algorithm Pairs {
   variables pair_set = { <<a,b>> \in {<<i, j>> : i, j \in int_set, k \in int_set} : a<b } ;    
   { 
      print pair_set;
   }
}

********)
\* BEGIN TRANSLATION (chksum(pcal) = "3e9add10" /\ chksum(tla) = "55598add")
VARIABLES pc, pair_set

vars == << pc, pair_set >>

Init == (* Global variables *)
        /\ pair_set = { <<a,b>> \in {<<i, j>> : i, j \in int_set, k \in int_set} : a<b }
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT(pair_set)
         /\ pc' = "Done"
         /\ UNCHANGED pair_set

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 



=============================================================================
\* Modification History
\* Last modified Sat Mar 22 20:27:35 GET 2025 by developer
\* Last modified Sun Jan 10 12:01:14 PST 2021 by lamport
\* Created Fri Jan 08 16:30:13 PST 2021 by lamport
