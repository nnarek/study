------------------------------ MODULE Session7_pz1 ------------------------------
EXTENDS Integers

(*********

--algorithm Add2FGSem {
   variable x = 0, sem = 1 ; 
   process (AB \in {3,-7}) 
    variable t = -1 ;
     {
     (*
        lock: await sem = 1 ;
              sem := 0 ;
     *) 
        lock: sem := sem - 1 ;
              await sem = 0 ;
        ab1: t := x ;
        ab2: x := t + 1;
     unlock: sem := 1 ;
     }
 }

*********)
\* BEGIN TRANSLATION (chksum(pcal) = "a8e4ebdb" /\ chksum(tla) = "6cefbfb")
VARIABLES pc, x, sem, t

vars == << pc, x, sem, t >>

ProcSet == ({3,-7})

Init == (* Global variables *)
        /\ x = 0
        /\ sem = 1
        (* Process AB *)
        /\ t = [self \in {3,-7} |-> -1]
        /\ pc = [self \in ProcSet |-> "lock"]

lock(self) == /\ pc[self] = "lock"
              /\ sem' = sem - 1
              /\ sem' = 0
              /\ pc' = [pc EXCEPT ![self] = "ab1"]
              /\ UNCHANGED << x, t >>

ab1(self) == /\ pc[self] = "ab1"
             /\ t' = [t EXCEPT ![self] = x]
             /\ pc' = [pc EXCEPT ![self] = "ab2"]
             /\ UNCHANGED << x, sem >>

ab2(self) == /\ pc[self] = "ab2"
             /\ x' = t[self] + 1
             /\ pc' = [pc EXCEPT ![self] = "unlock"]
             /\ UNCHANGED << sem, t >>

unlock(self) == /\ pc[self] = "unlock"
                /\ sem' = 1
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << x, t >>

AB(self) == lock(self) \/ ab1(self) \/ ab2(self) \/ unlock(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {3,-7}: AB(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Mon Mar 24 15:46:46 GET 2025 by developer
\* Last modified Fri Feb 12 09:46:15 PST 2021 by lamport
\* Created Fri Feb 12 09:44:05 PST 2021 by lamport
