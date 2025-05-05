---- MODULE MC ----
EXTENDS Session6_ex2, TLC

\* CONSTANT definitions @modelParameterConstants:0Nset
const_1742802289061500000 == 
{1,2,5,7,10}
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1742802289061501000 ==
(pc = "Done") => (x = N^2)
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1742802289061502000 ==
/\ x \in 0..N^2
/\ i \in 0..N
/\ pc \in {"a", "b", "Done"}
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1742802289061503000 ==
/\ pc = "b" => x = (i-1)^2
/\ pc /= "b" => x = i^2
(* invariant will be short without implicit actiona "a" and "b" *)
----
=============================================================================
\* Modification History
\* Created Mon Mar 24 11:44:49 GET 2025 by developer
