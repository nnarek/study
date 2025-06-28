------------------------------ MODULE Session6_ex2 ------------------------------
EXTENDS Integers, TLC

CONSTANT Nset
ASSUME Nset \subseteq Nat

(*********

--algorithm Square2  {
  variable x = 0, i = 0, N \in Nset ;
  { a: while (i < N) {
           i := i + 1  ;
        b: x := x + (2*i - 1) ;
       } ;
     (* i := ""; *)
  }
}

*********)
\* BEGIN TRANSLATION (chksum(pcal) = "acb46584" /\ chksum(tla) = "10388154")
VARIABLES pc, x, i, N

vars == << pc, x, i, N >>

Init == (* Global variables *)
        /\ x = 0
        /\ i = 0
        /\ N \in Nset
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF i < N
           THEN /\ i' = i + 1
                /\ pc' = "b"
           ELSE /\ pc' = "Done"
                /\ i' = i
     /\ UNCHANGED << x, N >>

b == /\ pc = "b"
     /\ x' = x + (2*i - 1)
     /\ pc' = "a"
     /\ UNCHANGED << i, N >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Mon Mar 24 11:32:30 GET 2025 by developer
\* Last modified Sun Jan 17 16:54:37 PST 2021 by lamport
\* Created Sun Jan 17 14:43:02 PST 2021 by claus
