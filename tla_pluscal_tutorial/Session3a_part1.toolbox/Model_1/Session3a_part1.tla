------------------------------ MODULE Session3a_part1 -------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT mset, nset
ASSUME /\ mset \subseteq Int
       /\ nset \subseteq Int
       /\ \A n \in nset : 0 <= n 
       /\ \A n \in nset, m \in mset : ~( n=0 /\ m=0 )

(*********

--algorithm Power {
   variable n \in nset, m \in mset,  i = 0 , res = 1 ;    
   { 
     assert 0 <= n /\ ( n/=0 \/ m/=0 );
     while (i < n) {
       res := res * m ;
       i := i + 1
     } ;
     assert res = m ^ n ;
   }
}

********)
\* BEGIN TRANSLATION (chksum(pcal) = "f90a8030" /\ chksum(tla) = "f3163f36")
VARIABLES pc, n, m, i, res

vars == << pc, n, m, i, res >>

Init == (* Global variables *)
        /\ n \in nset
        /\ m \in mset
        /\ i = 0
        /\ res = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(0 <= n /\ ( n/=0 \/ m/=0 ), 
                   "Failure of assertion at line 15, column 6.")
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << n, m, i, res >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF i < n
               THEN /\ res' = res * m
                    /\ i' = i + 1
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(res = m ^ n, 
                              "Failure of assertion at line 20, column 6.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << i, res >>
         /\ UNCHANGED << n, m >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

===========================================
\* Modification History
\* Last modified Fri Mar 21 22:10:29 GET 2025 by developer
\* Created Fri Dec 25 11:48:28 PST 2020 by claus
