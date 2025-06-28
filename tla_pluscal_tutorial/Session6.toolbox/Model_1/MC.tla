---- MODULE MC ----
EXTENDS Session6, TLC

\* CONSTANT definitions @modelParameterConstants:0N
const_1610929319093406000 == 
2
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1610929319093407000 ==
(pc = "Done") => (x /= N^2)
----
=============================================================================
\* Modification History
\* Created Sun Jan 17 16:21:59 PST 2021 by lamport
