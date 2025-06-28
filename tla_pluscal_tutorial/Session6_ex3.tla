------------------------------ MODULE Session6_ex3 ------------------------------
EXTENDS Integers, TLC

CONSTANT Nset
ASSUME Nset \subseteq Nat

(*********

--algorithm Square2  {
  variable N \in Nset, x = [j \in 0..N |-> 0], i = 0;
  { a: while (i < N) {
           i := i + 1  ;
        b: x[i] := x[i-1] + (2*i - 1) ;
       } ;
     print x;
  }
}

*********)
\* BEGIN TRANSLATION (chksum(pcal) = "288666df" /\ chksum(tla) = "ac936b85")
VARIABLES pc, N, x, i

vars == << pc, N, x, i >>

Init == (* Global variables *)
        /\ N \in Nset
        /\ x = [j \in 0..N |-> 0]
        /\ i = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF i < N
           THEN /\ i' = i + 1
                /\ pc' = "b"
           ELSE /\ PrintT(x)
                /\ pc' = "Done"
                /\ i' = i
     /\ UNCHANGED << N, x >>

b == /\ pc = "b"
     /\ x' = [x EXCEPT ![i] = x[i-1] + (2*i - 1)]
     /\ pc' = "a"
     /\ UNCHANGED << N, i >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Mon Mar 24 12:01:24 GET 2025 by developer
\* Last modified Sun Jan 17 16:54:37 PST 2021 by lamport
\* Created Sun Jan 17 14:43:02 PST 2021 by claus
