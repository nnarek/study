---- MODULE MC ----
EXTENDS Session7_pz1, TLC

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1742816827031540000 ==
(pc[3] = "Done") /\ (pc[-7] = "Done") => (x = 2)
----
=============================================================================
\* Modification History
\* Created Mon Mar 24 15:47:07 GET 2025 by developer
