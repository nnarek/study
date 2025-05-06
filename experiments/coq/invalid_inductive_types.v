

Theorem O_neq_S : forall n : nat, O <> S n.
Proof.
  intros.
  unfold not.
  intros.
  discriminate H.
  Show Proof.
Qed.

Search (forall n : nat, O <> S n).
Print O_S.


Check nat_ind.



Module EmptyTypes.

(* Inductive fff : Prop :=
  | cu : (fff -> False) -> fff. *)
    
Inductive cyclic_type : Prop :=
| absurd_constructor : cyclic_type -> cyclic_type.

Check cyclic_type_ind.
Check cyclic_type_exhaustive.

Lemma instance_of_cyclic_type_does_not_exists : cyclic_type -> False.
Proof.
  intros.
  induction H.
  Show Proof.
  assumption.
  Show Proof.
Qed.

Inductive absurd_type : Prop :=
 | cu : absurd_type -> False -> absurd_type.

Check absurd_type_ind.

Lemma absurd_type_is_empty : absurd_type <-> False.
Proof.
  split; intros; induction H. auto. 
Qed.

End EmptyTypes.






Module ParCoq.
Fail Inductive paradox : Prop :=
| paradox_intro : (paradox -> False) -> paradox.

(* since constructor of paradox is reqursive and only one then its mean that we can not construct it. if we can not construct then it is empty. if so then it is mean that (paradox -> False) holds which also lead that paradox should have instance *)
(* this is contradiction and coq does not allow such types *)
(*TODO learn more about strict positivity requirement of coq *)

(*TODO why this one also does not allowed *)
Fail Inductive paradox1 : Prop :=
| par_el : paradox1
| paradox1_intro : (paradox1 -> False) -> paradox1.

(* this proves that paradox type is empty *)
Fail Definition paradox_is_empty (p : paradox) : False :=
  match p with
    | paradox_intro f => f p
  end.

(* this proves False *)
Theorem contr : False.
Proof.
  Fail apply (paradox_is_empty (con paradox_is_empty)).
Abort.
End ParCoq.







(* same proof as in par_coq module but will be validated by coq proofchecker *)
Module ParAxiomatic.

Axiom par : Prop. (* declaration of type par *)
Axiom con : (par -> False) -> par. (* constructor of par *)
Axiom par_inv : forall (p:par), exists f, p = con f. (* par can be constructed only with constructor con. match expression of inductive types of coq always assume this axiom *)

Theorem par_is_empty : par -> False.
Proof.
  intros p.
  destruct (par_inv p) as [pf He].
  apply (pf p).
Qed.

Theorem contr : False.
Proof.
  apply (par_is_empty (con par_is_empty)).
Qed.

End ParAxiomatic.






Module MutualLemmas.

Fail Inductive TypeA : Prop :=
  | ConstructorA : TypeB -> TypeA
with TypeB : Prop :=
  | ConstructorB : (TypeA -> False) -> TypeB. 
(* mutual inductive types also should be strict positive *)


Inductive TypeA : Prop :=
  | ConstructorA : TypeB -> TypeA
with TypeB : Prop :=
  | ConstructorB : TypeA -> TypeB. 

(* proof in functional style *)
Fixpoint TypeA_is_empty' (a : TypeA) : False :=
  match a with 
  | ConstructorA b' => TypeB_is_empty' b'
  end
with TypeB_is_empty' (b : TypeB) : False :=
  match b with 
  | ConstructorB a' => TypeA_is_empty' a'
  end.

(* definitions should be unfolded so that coq can find mutual inductive premises *)
Fail Lemma A_is_empty : ~TypeA
  with B_is_empty : ~TypeB.

Lemma A_is_empty' : TypeA -> False
  with B_is_empty' : TypeB -> False.
Proof.
  - apply A_is_empty'.
  - apply B_is_empty'.
Fail Qed.
Abort.

Lemma A_is_empty : TypeA -> False
  with B_is_empty : TypeB -> False.
Proof.
  - intros a. 
    inversion a as [b].
    apply (B_is_empty b).
  - intros b. 
    inversion b as [a].
    apply (A_is_empty a).
Qed.


Fixpoint A_is_empty' (a:TypeA) : False.
  enough (forall (b:TypeB), False) as B_is_empty'.
  - destruct a as [b]. apply (B_is_empty' b).
  - intros b. destruct b as [a']. apply (A_is_empty' a').
Defined.

End MutualLemmas.




Module NegativeTerm.
(* from https://stackoverflow.com/questions/31226427/proving-false-with-negative-inductive-types-in-coq *)
Fail Inductive term : Set :=
| App : term -> term -> term
| Abs : (term -> term) -> term.

Fail Definition uhoh (t : term) : term :=
  match t with
    | Abs f => f t
    | _ => t
  end.

(* Inductive orr (A B : Prop) : Prop :=
  orr_introl : A -> orr A B | orr_intror : B -> orr A B. *)

Theorem aa : ~ (exists n: nat, forall m, n <> m).
Proof.
  unfold not.
  intros [n H].
  eapply H.
  reflexivity.
Qed.



Fail Definition uhoh (tn: term) : False  :=
  match tn with
    | Abs f => (f t)
    | _ => tn
  end.


Fail Check uhoh (Abs (fun (t : term) => proj2 (uhoh t))).

Axiom term : Prop.
Axiom App : term -> term -> term.
Axiom Abs : (term -> term) -> term.
(* we can not use \/ here https://proofassistants.stackexchange.com/questions/1686/how-can-i-use-a-three-terms-decidable-axiom-in-a-case-analysis*)
(* but almost same axiom works in ParAxiomatic even if I add \/ *)
Axiom term_inv' : forall (t:term), (exists p1 p2, t = App p1 p2) \/ (exists f, t = Abs f).
Axiom term_inv : forall (t:term), {p1 : term & {p2 : term | t = App p1 p2}} + {f : term -> term | t = Abs f}.

(* if we can prove that term is empty then we can use uhoh to prove False, but term is not empty *)
Theorem term_exists : term.
Proof.
  apply (Abs (fun p => p)).
Qed.

(* we can try to count number of nested recursive calls and prove False by proving that such number does not exists *)
Fail Definition uhoh (t : term) (n : nat) : term * nat
  := match (term_inv t) with
    | or_introl x => (t , n)
    | or_intror x => (t , n)
  end. 

Definition infinite_fun (t : term) (n : nat) : term * nat.
Proof.
  specialize (term_inv t) as H.
  destruct H.
  - auto.
  - destruct s.  


Abort.

Fail Check uhoh (Abs (fun (t : term) => proj1 (uhoh t 0) )) 0.
(* but this will not count number of calls *)