------------------------------ MODULE Session4_pz2 ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT mset
ASSUME mset \subseteq Int
ASSUME \A S \in SUBSET mset : {(x \in S) : x \in S} = (IF S = {} THEN {} ELSE {TRUE})



=============================================================================
\* Modification History
\* Last modified Sun Mar 23 15:43:16 GET 2025 by developer
\* Last modified Sun Jan 10 12:01:14 PST 2021 by lamport
\* Created Fri Jan 08 16:30:13 PST 2021 by lamport
