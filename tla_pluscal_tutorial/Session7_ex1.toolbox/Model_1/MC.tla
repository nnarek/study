---- MODULE MC ----
EXTENDS Session7_ex1, TLC

\* CONSTANT definitions @modelParameterConstants:0Nset
const_1742820874562640000 == 
0..8
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1742820874562641000 ==
(\A id \in ProcSet : pc[id] = "Done") => (x = N)
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1742820874562642000 ==
\A id1,id2 \in ProcSet : ( (id1/=id2 /\ pc[id1]=pc[id2]) => pc[id1] \in {"Done","lock"})
----
=============================================================================
\* Modification History
\* Created Mon Mar 24 16:54:34 GET 2025 by developer
