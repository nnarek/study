---- MODULE MC ----
EXTENDS Session7, TLC

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1742815882403528000 ==
(pc[3] = "Done") /\ (pc[-7] = "Done") => (x = 2)
----
=============================================================================
\* Modification History
\* Created Mon Mar 24 15:31:22 GET 2025 by developer
