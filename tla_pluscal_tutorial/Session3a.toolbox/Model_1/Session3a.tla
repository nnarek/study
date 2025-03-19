------------------------------ MODULE Session3a -------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT None
ASSUME None \notin Int

(*********  

--algorithm TupleMax {
   variables inp = <<1, 3, 2>>, max = None, i = 2 ;    
   { if (inp /= << >>) {
       max := inp[1] ;
       while (i =< Len(inp)) {
         if (inp[i] > max) { max := inp[i] } ;
         i := i + 1
       } 
     } ;
     assert IF inp = << >> THEN max = None
                           ELSE    (\E n \in 1..Len(inp) : max = inp[n])
                                /\ (\A n \in 1..Len(inp) : max > inp[n])
   }
}

********)
\* BEGIN TRANSLATION (chksum(pcal) = "c030ee5a" /\ chksum(tla) = "1da560d6")
VARIABLES inp, max, i, pc

vars == << inp, max, i, pc >>

Init == (* Global variables *)
        /\ inp = <<1, 3, 2>>
        /\ max = None
        /\ i = 2
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF inp /= << >>
               THEN /\ max' = inp[1]
                    /\ pc' = "Lbl_2"
               ELSE /\ pc' = "Lbl_3"
                    /\ max' = max
         /\ UNCHANGED << inp, i >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF i =< Len(inp)
               THEN /\ IF inp[i] > max
                          THEN /\ max' = inp[i]
                          ELSE /\ TRUE
                               /\ max' = max
                    /\ i' = i + 1
                    /\ pc' = "Lbl_2"
               ELSE /\ pc' = "Lbl_3"
                    /\ UNCHANGED << max, i >>
         /\ inp' = inp

Lbl_3 == /\ pc = "Lbl_3"
         /\ Assert(IF inp = << >> THEN max = None
                                  ELSE    (\E n \in 1..Len(inp) : max = inp[n])
                                       /\ (\A n \in 1..Len(inp) : max > inp[n]), 
                   "Failure of assertion at line 18, column 6.")
         /\ pc' = "Done"
         /\ UNCHANGED << inp, max, i >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
===========================================
\* Modification History
\* Last modified Fri Jan 08 17:24:21 PST 2021 by lamport
\* Last modified Sat Dec 26 11:48:57 PST 2020 by claus
\* Created Fri Dec 25 11:48:28 PST 2020 by claus
