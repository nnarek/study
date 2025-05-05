---- MODULE MC ----
EXTENDS Session8_ex1_ex2, TLC

\* CONSTANT definitions @modelParameterConstants:0N
const_1742823087070675000 == 
7
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1742823087070676000 ==
~ (\E id1,id2 \in Procs : id1/=id2 /\ pc[id1]="cs" /\ pc[id2]="cs")
----
=============================================================================
\* Modification History
\* Created Mon Mar 24 17:31:27 GET 2025 by developer
