The module begins with a string of four or more - characters. Text that
precedes the module is ignored.

------------------------------- MODULE Session2 -------------------------------
EXTENDS Integers, TLC
 
(********

--algorithm AnyName1 {
    variable x = <<1, 2, 3>> , y = x ;    
    {  
      x[3] := x[2] + 4 ;
      print x  ;
      print y
    }
}


********)


\* BEGIN TRANSLATION (chksum(pcal) = "c93cd468" /\ chksum(tla) = "43e17a25")
VARIABLES pc, x, y

vars == << pc, x, y >>

Init == (* Global variables *)
        /\ x = <<1, 2, 3>>
        /\ y = x
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ x' = [x EXCEPT ![3] = x[2] + 4]
         /\ PrintT(x')
         /\ PrintT(y)
         /\ pc' = "Done"
         /\ y' = y

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

\* This is a single-line comment.  
\* The module is ended by a string of four or more = characters.  
===============================================================================
Text that follows the module is ignored.  The Toolbox maintains the following 
information.

\* Modification History
\* Last modified Wed Mar 19 22:04:21 GET 2025 by developer
\* Last modified Tue Dec 22 16:15:06 PST 2020 by lamport
\* Created Sat Dec 05 17:41:14 PST 2020 by lamport
