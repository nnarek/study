------------------------------ MODULE Session8_ex3 ------------------------------
EXTENDS Integers

CONSTANT N
CONSTANT Procs
ASSUME N \in Int

(*********

--algorithm 1BitProtocol {
    variables flag = [i \in Procs |-> FALSE] ;
    process (P \in Procs) {
     ncs: while (TRUE) {
            skip ; 
     enter: flag[self] := TRUE ; 
        e2: await ~ flag[1 - self] ;
        cs: skip ;
      exit: flag[self] := FALSE ;            
    }
  }
}

*********)
\* BEGIN TRANSLATION (chksum(pcal) = "d13d0d69" /\ chksum(tla) = "7bec331e")
VARIABLES pc, flag

vars == << pc, flag >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ flag = [i \in Procs |-> FALSE]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "enter"]
             /\ flag' = flag

enter(self) == /\ pc[self] = "enter"
               /\ flag' = [flag EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "e2"]

e2(self) == /\ pc[self] = "e2"
            /\ ~ flag[1 - self]
            /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ flag' = flag

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ flag' = flag

exit(self) == /\ pc[self] = "exit"
              /\ flag' = [flag EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "ncs"]

P(self) == ncs(self) \/ enter(self) \/ e2(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Procs: P(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Tue Mar 25 14:31:01 GET 2025 by developer
\* Last modified Fri Feb 12 09:46:15 PST 2021 by lamport
\* Created Fri Feb 12 09:44:05 PST 2021 by lamport
