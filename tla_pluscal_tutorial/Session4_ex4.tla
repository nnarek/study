------------------------------ MODULE Session4_ex4 ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT max_len 

(*********  

--algorithm ABC_tuple {
   { 
      (*print  { t \subseteq Seq({"a","b","c"}) : Len(t)<=max_len } *)
      print UNION { [1..n -> {"a","b","c"}] : n \in 0..max_len }
   }
}

********)
\* BEGIN TRANSLATION (chksum(pcal) = "af21c641" /\ chksum(tla) = "dc2b905d")
VARIABLE pc

vars == << pc >>

Init == /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT(UNION { [1..n -> {"a","b","c"}] : n \in 0..max_len })
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 



=============================================================================
\* Modification History
\* Last modified Sun Mar 23 16:42:09 GET 2025 by developer
\* Last modified Sun Jan 10 12:01:14 PST 2021 by lamport
\* Created Fri Jan 08 16:30:13 PST 2021 by lamport
