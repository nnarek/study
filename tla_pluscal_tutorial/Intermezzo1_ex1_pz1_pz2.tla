----------------------------- MODULE Intermezzo1_ex1_pz1_pz2 -----------------------------
EXTENDS Integers, Sequences, TLC


RemoveElt(n, seq) == SubSeq(seq,1,n-1) \o SubSeq(seq,n+1,Len(seq))
ASSUME RemoveElt(2,<<1,2>>) = <<1>>
ASSUME \A s \in UNION {[1..i -> 1..10] : i \in 1..4} : RemoveElt(1,s) = Tail(s)


MyTail(seq) == IF Len(seq) = 0 THEN 0+"seq should be non empty" ELSE [i \in 1..(Len(seq)-1) |-> seq[i+1]]
ASSUME \A s \in UNION {[1..i -> 1..10] : i \in 1..4} :  MyTail(s) = Tail(s)


(*ASSUME Seq({}) = {<<>>}*)
ASSUME <<>> \in Seq({}) (*only member is <<>> empty sequence*)
ASSUME {<<>>} \subseteq Seq({})

(*********

--algorithm Out {
  {
    print Seq({});
  }
}

*********)
\* BEGIN TRANSLATION (chksum(pcal) = "c6ffe284" /\ chksum(tla) = "c3f9794e")
VARIABLE pc

vars == << pc >>

Init == /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT(Seq({}))
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
\* Last modified Tue Mar 25 15:18:08 GET 2025 by developer
\* Created Tue Mar 25 12:55:48 GET 2025 by developer
   
