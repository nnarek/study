------------------------------ MODULE Session3a_part2 -------------------------------
EXTENDS Integers, Sequences, TLC


\* TODO check for all pairs {0..7}*{-8..8} except (0,0)
CONSTANT mset, nset
ASSUME /\ mset \subseteq Int
       /\ nset \subseteq Int
       /\ \A n \in nset : 0 <= n 
       /\ \A n \in nset, m \in mset : ~( n=0 /\ m=0 )


(*********

--algorithm Power {
   variable n \in nset, m \in mset, res = 1, pow = m, n_init = n ;    
   { 
     assert 0 <= n /\ ( n/=0 \/ m/=0 );
     while (0 < n) {
       if(n%2=1) {
         res := res * pow ;
       };
       pow := pow*pow; 
       n := n \div 2;
     };
     assert res = m ^ n_init ;
   }
}

********)
\* BEGIN TRANSLATION (chksum(pcal) = "e459aeac" /\ chksum(tla) = "9fb2c351")
VARIABLES pc, n, m, res, pow, n_init

vars == << pc, n, m, res, pow, n_init >>

Init == (* Global variables *)
        /\ n \in nset
        /\ m \in mset
        /\ res = 1
        /\ pow = m
        /\ n_init = n
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(0 <= n /\ ( n/=0 \/ m/=0 ), 
                   "Failure of assertion at line 18, column 6.")
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << n, m, res, pow, n_init >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF 0 < n
               THEN /\ IF n%2=1
                          THEN /\ res' = res * pow
                          ELSE /\ TRUE
                               /\ res' = res
                    /\ pow' = pow*pow
                    /\ n' = (n \div 2)
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(res = m ^ n_init, 
                              "Failure of assertion at line 26, column 6.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << n, res, pow >>
         /\ UNCHANGED << m, n_init >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

===========================================
\* Modification History
\* Last modified Sat Mar 22 16:54:33 GET 2025 by developer
\* Created Fri Dec 25 11:48:28 PST 2020 by claus
