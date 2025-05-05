------------------------------ MODULE Session4_ex5 ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT int_set
ASSUME int_set \subseteq Int
(*
ASSUME  \A S \in int_set,T \in int_set,U \in int_set : (S \X T) \X U = {<< <<s,t>>, u>> : s \in S, t \in T, u \in U}
*)

(*********  

--algorithm 3Product {
   variables S \in int_set,T \in int_set,U \in int_set ;    
   { 
      (*TODO assert (S \X T) \X U = {<< <<s,t>>, u>> : s \in S, t \in T, u \in U};*)
      assert TRUE;
   }
}

********)
\* BEGIN TRANSLATION (chksum(pcal) = "71fa7e98" /\ chksum(tla) = "aefb9d11")
VARIABLES pc, S, T, U

vars == << pc, S, T, U >>

Init == (* Global variables *)
        /\ S \in int_set
        /\ T \in int_set
        /\ U \in int_set
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(TRUE, "Failure of assertion at line 16, column 7.")
         /\ pc' = "Done"
         /\ UNCHANGED << S, T, U >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 



=============================================================================
\* Modification History
\* Last modified Sun Mar 23 23:00:58 GET 2025 by developer
\* Last modified Sun Jan 10 12:01:14 PST 2021 by lamport
\* Created Fri Jan 08 16:30:13 PST 2021 by lamport
