------------------------------ MODULE Session4_ex1 ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT Tuples, minValue
ASSUME /\ Tuples \subseteq Seq(Int)
       /\ minValue \in Int
       /\ \A t \in Tuples : \A i \in 1..Len(t) : t[i] > minValue 

(*********  

--algorithm SillyTupleMax {
   variables inp \in Tuples, k = 1, max = minValue, I = 1..Len(inp) ;    
   { 
     while (k =< Len(inp)) {
       if (inp[k] > max) { max := inp[k] } ;
       k := k + 1
     } ;
     
     while (I /= {}) {
       with (i \in I) {
         if (inp[i] = max) { I := {} } ;
         else { I := I \ {i} }
       }
     } ;
     assert IF inp = << >> THEN max = minValue
                           ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
                                /\ \A n \in 1..Len(inp) : max >= inp[n]
   }
}

********)
\* BEGIN TRANSLATION (chksum(pcal) = "258c7cdd" /\ chksum(tla) = "ce1a68eb")
VARIABLES pc, inp, k, max, I

vars == << pc, inp, k, max, I >>

Init == (* Global variables *)
        /\ inp \in Tuples
        /\ k = 1
        /\ max = minValue
        /\ I = 1..Len(inp)
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF k =< Len(inp)
               THEN /\ IF inp[k] > max
                          THEN /\ max' = inp[k]
                          ELSE /\ TRUE
                               /\ max' = max
                    /\ k' = k + 1
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Lbl_2"
                    /\ UNCHANGED << k, max >>
         /\ UNCHANGED << inp, I >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF I /= {}
               THEN /\ \E i \in I:
                         IF inp[i] = max
                            THEN /\ I' = {}
                            ELSE /\ I' = I \ {i}
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(IF inp = << >> THEN max = minValue
                                             ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
                                                  /\ \A n \in 1..Len(inp) : max >= inp[n], 
                              "Failure of assertion at line 25, column 6.")
                    /\ pc' = "Done"
                    /\ I' = I
         /\ UNCHANGED << inp, k, max >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 



=============================================================================
\* Modification History
\* Last modified Sat Mar 22 18:55:37 GET 2025 by developer
\* Last modified Sun Jan 10 12:01:14 PST 2021 by lamport
\* Created Fri Jan 08 16:30:13 PST 2021 by lamport
