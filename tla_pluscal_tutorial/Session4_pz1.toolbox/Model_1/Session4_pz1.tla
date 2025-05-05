------------------------------ MODULE Session4_pz1 ------------------------------
EXTENDS Integers, Sequences, TLC


Intersect(S) == {x \in UNION S : (\A s \in S : x \in s)} 

(*********  

--algorithm Intersections {
   { 
      assert Intersect({{1,2},{2,3}}) = {2};
      assert Intersect({{1,4},{2,3}}) = {};
      assert Intersect({{1,3,2,3},{1,3,3}}) = {1,3};
   }
}

********)
\* BEGIN TRANSLATION (chksum(pcal) = "9f4bdd2e" /\ chksum(tla) = "474ac88b")
VARIABLE pc

vars == << pc >>

Init == /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(Intersect({{1,2},{2,3}}) = {2}, 
                   "Failure of assertion at line 11, column 7.")
         /\ Assert(Intersect({{1,4},{2,3}}) = {}, 
                   "Failure of assertion at line 12, column 7.")
         /\ Assert(Intersect({{1,3,2,3},{1,3,3}}) = {1,3}, 
                   "Failure of assertion at line 13, column 7.")
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 



=============================================================================
\* Modification History
\* Last modified Sun Mar 23 16:44:05 GET 2025 by developer
\* Last modified Sun Jan 10 12:01:14 PST 2021 by lamport
\* Created Fri Jan 08 16:30:13 PST 2021 by lamport
