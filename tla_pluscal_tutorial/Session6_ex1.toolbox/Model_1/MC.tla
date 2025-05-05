---- MODULE MC ----
EXTENDS Session6_ex1, TLC

\* CONSTANT definitions @modelParameterConstants:0Nset
const_1742803085277511000 == 
{1,2,3,5,10}
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1742803085277512000 ==
(pc = "Done") => (x = N^2)
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1742803085277513000 ==
/\ x \in 0..N^2
/\ i \in 0..N
/\ pc \in {"a", "b", "Done"}
----
=============================================================================
\* Modification History
\* Created Mon Mar 24 11:58:05 GET 2025 by developer
