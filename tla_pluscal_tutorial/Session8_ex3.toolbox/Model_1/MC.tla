---- MODULE MC ----
EXTENDS Session8_ex3, TLC

\* CONSTANT definitions @modelParameterConstants:0Procs
const_17428990069991084000 == 
{0,1}
----

\* CONSTANT definitions @modelParameterConstants:1N
const_17428990069991085000 == 
2
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_17428990069991086000 ==
~ (\E id1,id2 \in Procs : id1/=id2 /\ pc[id1]="cs" /\ pc[id2]="cs")
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_17428990069991087000 ==
/\ (\E id1 \in Procs : pc[id1]="cs" => (\A id2 \in Procs : (id1/=id2) => (~(~ flag[1 - id2])))) (*if there exists processes in cs then await conditions of others are false*)
/\ (\E id1 \in Procs : pc[id1]="cs" => (\A id2 \in Procs: (id1/=id2) => ((~ flag[1 - id2]) <=> (pc[id2]="cs")))) (*if there  processes in cs then other process is in cs if only if its await condition is true*)
----
=============================================================================
\* Modification History
\* Created Tue Mar 25 14:36:46 GET 2025 by developer
