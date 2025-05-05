---- MODULE MC ----
EXTENDS Session9_ex1, TLC

\* CONSTANT definitions @modelParameterConstants:0N
const_17429057299341294000 == 
7
----

\* CONSTANT definitions @modelParameterConstants:1Procs
const_17429057299341295000 == 
0..(N-1)
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_17429057299341296000 ==
~ (\E id1,id2 \in Procs : id1/=id2 /\ pc[id1]="cs" /\ pc[id2]="cs")
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_17429057299341297000 ==
\A self \in ProcSet : pc[self]="cs" => (self=turn)
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_17429057299341298000 ==
\A t \in 0..(N-1): []<>(pc[turn] = "cs" /\ turn=t)
(*means that each process enters to the critical section infinite many times*)
----
=============================================================================
\* Modification History
\* Created Tue Mar 25 16:28:49 GET 2025 by developer
