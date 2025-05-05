------------------------------ MODULE Session8_ex4 ------------------------------
EXTENDS Integers

CONSTANT N
CONSTANT Procs
ASSUME N \in Int

(*********

--algorithm 1BitMutex {
  variables flag = [i \in Procs |-> FALSE] ;
  process (P \in Procs) {
    ncs: while (TRUE) {
           skip ;
    enter: flag[self] := TRUE ; 
       e2: if (flag[1 - self]) {              
       e3:   if (self = 0) { goto e2 } 
             else {           
               flag[self] := FALSE ;
       e4:     await ~ flag[1 - self] ;
               goto enter ;              
              } 
           } ;
       cs: skip ;
     exit: flag[self] := FALSE            
    }
  }
}

*********)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "32af36e6")
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
            /\ IF flag[1 - self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "e3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ flag' = flag

e3(self) == /\ pc[self] = "e3"
            /\ IF self = 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "e2"]
                       /\ flag' = flag
                  ELSE /\ flag' = [flag EXCEPT ![self] = FALSE]
                       /\ pc' = [pc EXCEPT ![self] = "e4"]

e4(self) == /\ pc[self] = "e4"
            /\ ~ flag[1 - self]
            /\ pc' = [pc EXCEPT ![self] = "enter"]
            /\ flag' = flag

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ flag' = flag

exit(self) == /\ pc[self] = "exit"
              /\ flag' = [flag EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "ncs"]

P(self) == ncs(self) \/ enter(self) \/ e2(self) \/ e3(self) \/ e4(self)
              \/ cs(self) \/ exit(self)

Next == (\E self \in Procs: P(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Tue Mar 25 16:33:46 GET 2025 by developer
\* Last modified Fri Feb 12 09:46:15 PST 2021 by lamport
\* Created Fri Feb 12 09:44:05 PST 2021 by lamport
