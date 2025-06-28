------------------------------ MODULE Session8_ex1_ex2 ------------------------------
EXTENDS Integers

CONSTANT N
ASSUME N \in Int

(*********

--algorithm Alternate {
  variable Procs = 0..(N-1), turn \in Procs ;
  process (p \in Procs) {
    ncs: while (TRUE) {
           skip ;
  enter:   await turn = self ;
     cs:   skip ;
   exit:   turn := (turn+1)%N 
         }
  }  
}

*********)
\* BEGIN TRANSLATION (chksum(pcal) = "a9dbb8b8" /\ chksum(tla) = "e7d18468")
VARIABLES pc, Procs, turn

vars == << pc, Procs, turn >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ Procs = 0..(N-1)
        /\ turn \in Procs
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "enter"]
             /\ UNCHANGED << Procs, turn >>

enter(self) == /\ pc[self] = "enter"
               /\ turn = self
               /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ UNCHANGED << Procs, turn >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << Procs, turn >>

exit(self) == /\ pc[self] = "exit"
              /\ turn' = (turn+1)%N
              /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ Procs' = Procs

p(self) == ncs(self) \/ enter(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Procs: p(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Mon Mar 24 17:29:52 GET 2025 by developer
\* Last modified Fri Feb 12 09:46:15 PST 2021 by lamport
\* Created Fri Feb 12 09:44:05 PST 2021 by lamport
