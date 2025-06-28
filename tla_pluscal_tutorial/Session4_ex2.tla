------------------------------ MODULE Session4_ex2 ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT int_set
ASSUME int_set \subseteq Int


(*********  

--algorithm Primes {
   variables pset = { n \in int_set : n>1 /\ \A i \in 2..(n-1) : n%i/=0 } ;    
   { 
      assert 2 \in pset; (*TODO why this assertion can not be checked when int_set=Nat, because TLC only need to check is 2 satisfies to the condition of set *)
      assert 3 \in pset;
      assert 1 \notin pset;
      assert 4 \notin pset;
      assert 6 \notin pset;
      (*print pset*)
   }
}

********)
\* BEGIN TRANSLATION (chksum(pcal) = "121b9e3e" /\ chksum(tla) = "abeb2b67")
VARIABLES pc, pset

vars == << pc, pset >>

Init == (* Global variables *)
        /\ pset = { n \in int_set : n>1 /\ \A i \in 2..(n-1) : n%i/=0 }
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(2 \in pset, "Failure of assertion at line 13, column 7.")
         /\ Assert(3 \in pset, "Failure of assertion at line 14, column 7.")
         /\ Assert(1 \notin pset, 
                   "Failure of assertion at line 15, column 7.")
         /\ Assert(4 \notin pset, 
                   "Failure of assertion at line 16, column 7.")
         /\ Assert(6 \notin pset, 
                   "Failure of assertion at line 17, column 7.")
         /\ pc' = "Done"
         /\ pset' = pset

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 



=============================================================================
\* Modification History
\* Last modified Sat Mar 22 21:34:08 GET 2025 by developer
\* Last modified Sun Jan 10 12:01:14 PST 2021 by lamport
\* Created Fri Jan 08 16:30:13 PST 2021 by lamport
