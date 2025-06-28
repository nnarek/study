------------------------------ MODULE Session9_ex1 ------------------------------
EXTENDS Integers

CONSTANT N
CONSTANT Procs
ASSUME N \in Int

(*********

--algorithm Alternate {
  variable  turn \in Procs ;
  fair process (p \in Procs) {
    ncs: while (TRUE) {
           skip ;
  enter:   await turn = self ;
     cs:   skip ;
   exit:   turn := (turn+1)%N 
         }
  }  
}

*********)
\* BEGIN TRANSLATION (chksum(pcal) = "46108b3" /\ chksum(tla) = "11531ebe")
VARIABLES pc, turn

vars == << pc, turn >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ turn \in Procs
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "enter"]
             /\ turn' = turn

enter(self) == /\ pc[self] = "enter"
               /\ turn = self
               /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ turn' = turn

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ turn' = turn

exit(self) == /\ pc[self] = "exit"
              /\ turn' = (turn+1)%N
              /\ pc' = [pc EXCEPT ![self] = "ncs"]

p(self) == ncs(self) \/ enter(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Procs: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Tue Mar 25 16:24:44 GET 2025 by developer
\* Last modified Fri Feb 12 09:46:15 PST 2021 by lamport
\* Created Fri Feb 12 09:44:05 PST 2021 by lamport
