------------------------------- MODULE Session3 -------------------------------
EXTENDS Integers, Sequences, TLC

(*********

--algorithm TupleMax {
   variables inp = <<1, 3, 2>>,  max = -99999, i = 1 ;    
   { 
     assert  \A n \in 1..Len(inp) : inp[n] > -99999 ;
     while (i =< Len(inp)) {
       if (inp[i] > max) { max := inp[i] } ;
       i := i + 1
     } ;
     assert    (\E n \in 1..Len(inp) : max = inp[n])
            /\ (\A n \in 1..Len(inp) : max >= inp[n])  
   }
}

********)

===========================================
\* Modification History
\* Last modified Sat Dec 26 11:48:57 PST 2020 by claus
\* Created Fri Dec 25 00:00:00 PST 2020 by claus

