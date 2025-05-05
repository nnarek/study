---- MODULE MC ----
EXTENDS Session9_ex2, TLC

\* CONSTANT definitions @modelParameterConstants:0Procs
const_17429123496031361000 == 
0..(N-1)
----

\* CONSTANT definitions @modelParameterConstants:1N
const_17429123496031362000 == 
2
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_17429123496031363000 ==
(pc[0] = "enter") ~> (pc[0] = "cs")
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_17429123496031364000 ==
  (\E i \in Procs : pc[i] = "enter") ~> (\E i \in Procs : pc[i] = "cs")
----
=============================================================================
\* Modification History
\* Created Tue Mar 25 18:19:09 GET 2025 by developer
