------------------------------ MODULE Session4_ex6 ------------------------------
EXTENDS Integers, Sequences, TLC



(*********  

--algorithm 1Tuples {
   variables S = {0,1,2,3} ;    
   { 
      print {<< x >> : x \in S};
      print [{1} -> S];
   }
}

********)
\* BEGIN TRANSLATION (chksum(pcal) = "3c63320d" /\ chksum(tla) = "d817b6bb")
VARIABLES pc, S

vars == << pc, S >>

Init == (* Global variables *)
        /\ S = {0,1,2,3}
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT({<< x >> : x \in S})
         /\ PrintT([{1} -> S])
         /\ pc' = "Done"
         /\ S' = S

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Sun Mar 23 16:43:40 GET 2025 by developer
\* Last modified Sun Jan 10 12:01:14 PST 2021 by lamport
\* Created Fri Jan 08 16:30:13 PST 2021 by lamport
