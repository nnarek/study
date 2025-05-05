------------------------------ MODULE Session7 ------------------------------
EXTENDS Integers

(*********

--algorithm Add2 {    

  variable x = 0 ;

  process (A = 3) {
    a: x := x + 1 (*TODO why it does not work without a: label??*)
  }

  process (B = -7) {
    b: x := x + 1
  }
}

*********)
\* BEGIN TRANSLATION (chksum(pcal) = "c9009fa5" /\ chksum(tla) = "83c6f40c")
VARIABLES pc, x

vars == << pc, x >>

ProcSet == {3} \cup {-7}

Init == (* Global variables *)
        /\ x = 0
        /\ pc = [self \in ProcSet |-> CASE self = 3 -> "a"
                                        [] self = -7 -> "b"]

a == /\ pc[3] = "a"
     /\ x' = x + 1
     /\ pc' = [pc EXCEPT ![3] = "Done"]

A == a

b == /\ pc[-7] = "b"
     /\ x' = x + 1
     /\ pc' = [pc EXCEPT ![-7] = "Done"]

B == b

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == A \/ B
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Mon Mar 24 14:23:16 GET 2025 by developer
\* Last modified Fri Feb 12 09:46:15 PST 2021 by lamport
\* Created Fri Feb 12 09:44:05 PST 2021 by lamport
