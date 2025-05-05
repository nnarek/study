---- MODULE MC ----
EXTENDS Session6_ex3, TLC

\* CONSTANT definitions @modelParameterConstants:0Nset
const_1742803600867518000 == 
{2,6,11,12}
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1742803600867519000 ==
pc = "Done" => x = [j \in 0..N |-> j^2]
----
=============================================================================
\* Modification History
\* Created Mon Mar 24 12:06:40 GET 2025 by developer
