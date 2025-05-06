Require Import Arith.

(* proof of 2 step induction of nat is pretty simple in functional style while it is not trivial in tactic style  *)
Fixpoint nat_2_step_ind (P : nat -> Prop)
(p0 : P 0) (p1 : P 1) (pn2 : forall n, P n -> P (S (S n)) ) (n : nat) : P n :=
  match n with 
  |0 => p0
  |1 => p1
  |S (S n'') => pn2 n'' (nat_2_step_ind P p0 p1 pn2 n'')
  end. 



(* here is relatively easy proof in tactic style which is almost equivalent to functional one *)
Lemma nat_2_step_ind_fix (P : nat -> Prop) :
  P 0 -> P 1 ->
  (forall n, P n -> P (S (S n))) ->
  forall n, P n.
Proof.
  fix nat_2_step_ind_fix 4. (* 4th parameter is "n" *)
  intros p0 p1 pn2 n.
  destruct n.
  - apply p0.
  - destruct n.
    + apply p1.
    + Show Proof. apply pn2. Show Proof. apply nat_2_step_ind_fix; auto. 
Qed.
(* "fix" tactic make same theorem available but we should call it against structurally small terms to avoid from infinite recursion as in case of proofs in functional style *)
(* "4" mean that 4th parameter will be structurally decreased and correctness of recursion should be checked against it *)
(* we can use auto tactic only after structurally destructing "n" because otherwise auto will incorrectly apply "self" to prove goal with infinite recursion *)





Lemma nat_ind2' (P : nat -> Prop) :
  P 0 -> P 1 ->
  (forall n, P n -> P (S (S n))) ->
  forall n, P (S n) -> P n.
Proof.
  intros.
  destruct n; auto.
  induction n; auto.
  destruct n; auto.
Admitted.

Lemma nat_ind2 (P : nat -> Prop) :
  P 0 -> P 1 ->
  (forall n, P n -> P (S (S n))) ->
  forall n, P n.
Proof.
  intros.
  induction n; auto.
  destruct n; auto.
Abort.



(* let define inductive Prop which holds if given P prop satisfies for 0 and 1 and for S S n if n also satisfies *)
(* then we can prove that this is equivalent to P *)
(* TODO try to finish this technique *)
Inductive Sat (P: nat -> Prop) : nat -> Prop:=
  | s0 : P 0 -> Sat P 0
  | s1 : P 1 -> Sat P 1
  | s2n : forall n, Sat P n -> Sat P (S (S n)). 

Lemma iff_Sat : forall (P : nat -> Prop) (n : nat), Sat P n -> P n.
Proof.
  intros.
  induction H.
Admitted.








From Coq Require Import Lists.List.
Import ListNotations.

Module list2_func.
Lemma list_back_inversion : forall {X : Type} (l : list X), 
  l = [] \/ exists y l', l = l' ++ [y].
  induction l.
  - auto.
  - right. destruct IHl; subst.
    + exists a. exists []. reflexivity.
    + destruct H. destruct H. subst. exists x. exists (a::x0). reflexivity.
Qed. 

Theorem list_2_step_ind: forall (X : Type) (P : list X -> Prop),
  P [] -> (forall x, P [x]) -> (forall x y (l : list X), P l -> P (x :: l ++ [y])) -> forall l' : list X, P l'.
Proof.
  fix self 6.
  intros X P p0 px pxy l.
  destruct l.
  - apply p0.
  - destruct (list_back_inversion l).
    + subst. apply px.
    + destruct H. destruct H. subst. apply pxy. apply (self _ _ p0 px pxy).
  Show Proof.
Fail Qed.
Abort.
End list2_func.





Module list2_ind.
Inductive AppInd {X : Type} : list X -> list X -> list X -> Prop :=
  | app_nil : forall (l : list X) , AppInd [] l l
  | app_con : forall (l1 l2 l : list X) (x : X), AppInd l1 l2 l -> AppInd (x::l1) l2 (x::l). 

Lemma list_back_inversion_app_ind : forall {X : Type} (l : list X), 
  l = [] \/ exists y l', AppInd l' [y] l.
  induction l.
  - auto.
  - right. destruct IHl; subst.
    + exists a. exists []. apply app_nil.
    + destruct H. destruct H. exists x. exists (a::x0). apply app_con. assumption.
Qed. 

(* I was thinking that problem is with termination checker which is not able to understand that "l" is structurally smaller than "l ++ [y]", but seems like problem is with fix tactic which only check that l is becoming structurally smaller and not able to do it with AppInd too *)
Theorem list_2_step_app_ind: forall (X : Type) (P : list X -> Prop),
  P [] -> (forall x, P [x]) -> (forall x y (l l' : list X), AppInd (x::l) [y] l' -> P l -> P l' ) -> forall l' : list X, P l'.
Proof.
  fix self 6.
  intros X P p0 px pxy l.
  destruct l.
  - apply p0.
  - destruct (list_back_inversion_app_ind l).
    + subst. apply px.
    + destruct H. destruct H. apply (app_con _ _ _ x) in H. 
      apply pxy in H; try assumption.
      apply (self _ _ p0 px pxy).
Fail Qed.
Abort.

(* same proof for fixpoint give error that can not guess descreasing argument *)
Fixpoint list2_step_fixpoint (X : Type) (P : list X -> Prop) (p0 : P []) (px : forall x, P [x]) (pxy : forall x y (l l' : list X), AppInd (x::l) [y] l' -> P l -> P l') (l : list X) : P l.
Proof.
  destruct l.
  - apply p0.
  - destruct (list_back_inversion_app_ind l).
    + subst. apply px.
    + destruct H. destruct H. apply (app_con _ _ _ x) in H. 
      apply pxy in H; try assumption.
      apply (list2_step_fixpoint _ _ p0 px pxy).
  Show Proof.
Fail Qed.
Abort.

Require Import Program.Wf.
Require Import Coq.Program.Tactics.
Require Import Coq.Init.Wf.
Require Import Lia.
(* we can not define Fixpoint via ltac language and same time specify "measure" *)
Program Fixpoint list2_step_fixpoint (X : Type) (P : list X -> Prop) (p0 : P []) (px : forall x, P [x]) (pxy : forall x y (l : list X), P l -> P (x :: l ++ [y])) (l : list X) {measure (length l)} : (P l) := 
  match l with
  | [] => p0
  | x :: l1 =>
      match list2_func.list_back_inversion l1 with
      | or_introl x1 => eq_ind_r (fun l2 => P (x :: l2)) (px x) x1
      | or_intror x1 =>
          match x1 with
          | ex_intro _ x2 x3 => 
              match x3 with
              | ex_intro _ x5 x6 =>
                  eq_ind_r (fun l2  => P (x :: l2))
                  (pxy x x2 x5 (list2_step_fixpoint X P p0 px pxy x5)) x6
              end
          end
      end
  end.
Next Obligation.
  (* too hard :) *)
Admitted.


(* not able to make this works too, to be able to provide termination proof for program written in tactic language *)
Definition list2_step (self : forall (X : Type) (P : list X -> Prop),
  P [] -> (forall x, P [x]) -> (forall x y (l : list X), P l -> P (x :: l ++ [y])) -> forall l' : list X, P l') (X : Type) (P : list X -> Prop) (p0 : P []) (px : forall x, P [x]) (pxy : forall x y (l : list X), P l -> P (x :: l ++ [y])) (l : list X) : (P l).
Proof.
    destruct l.
  - apply p0.
  - destruct (list2_func.list_back_inversion l).
    + subst. apply px.
    + destruct H. destruct H. subst. apply pxy. apply (self _ _ p0 px pxy).
Qed.

Fail Program Fixpoint list2_step_fixpoint' (X : Type) (P : list X -> Prop) (p0 : P []) (px : forall x, P [x]) (pxy : forall x y (l : list X), P l -> P (x :: l ++ [y])) (l : list X) {measure (length l)} : (P l) := list2_step list2_step_fixpoint' X P p0 px pxy l.

(* coq not able to guess is length argument limited at bottom *)
Fixpoint list2_step_fixpoint_with_length_arg (X : Type) (P : list X -> Prop) (p0 : P []) (px : forall x, P [x]) (pxy : forall x y (l : list X), P l -> P (x :: l ++ [y])) (l : list X) (len : nat) {L: len = length l} : P l.
Proof.
  destruct l.
  - apply p0.
  - destruct (list2_func.list_back_inversion l).
      * subst. apply px.
      * destruct H. destruct H. subst l. apply pxy. 
      apply (list2_step_fixpoint_with_length_arg _ _ p0 px pxy x1 (len - 2)).
      simpl in *. inversion L. rewrite app_length. simpl. lia. 
Abort.

(* here coq can guess because we destruct len first *)
Fixpoint list2_step_fixpoint_with_length_arg (X : Type) (P : list X -> Prop) (p0 : P []) (px : forall x, P [x]) (pxy : forall x y (l : list X), P l -> P (x :: l ++ [y])) (l : list X) (len : nat) {L: len = length l} : P l.
Proof.
  destruct len; destruct l; simpl in *. 
  - apply p0.
  - inversion L.
  - inversion L.
  - destruct (list2_func.list_back_inversion l).
      * subst. apply px.
      * destruct H. destruct H. subst. apply pxy. 
      apply (list2_step_fixpoint_with_length_arg _ _ p0 px pxy x1 (len - 1)).
      simpl in *. inversion L. rewrite app_length. simpl. lia. 
Qed.

Theorem list_2_step: forall (X : Type) (P : list X -> Prop),
  P [] -> (forall x, P [x]) -> (forall x y (l : list X), P l -> P (x :: l ++ [y])) -> forall (l : list X), P l.
Proof.
  intros X P p0 px pxy l.
  apply (@list2_step_fixpoint_with_length_arg X P p0 px pxy l (length l) eq_refl).
Qed.


Theorem list_2_step_with_length_arg: forall (X : Type) (P : list X -> Prop),
  P [] -> (forall x, P [x]) -> (forall x y (l : list X), P l -> P (x :: l ++ [y])) -> forall (l : list X) (len : nat) {L: len = length l}, P l.
Proof.
  fix self 7.
  intros X P p0 px pxy l len leq.
  destruct len; destruct l; simpl in *. 
  - apply p0.
  - inversion leq.
  - inversion leq.
  - destruct (list2_func.list_back_inversion l).
      * subst. apply px.
      * destruct H. destruct H. subst. apply pxy. 
      apply (self _ _ p0 px pxy x1 (len - 1)).
      simpl in *. inversion leq. rewrite app_length. simpl. lia. 
Qed.

Theorem list_2_step_with_fix_tactic: forall (X : Type) (P : list X -> Prop),
  P [] -> (forall x, P [x]) -> (forall x y (l : list X), P l -> P (x :: l ++ [y])) -> forall (l : list X), P l.
Proof.
  intros X P p0 px pxy l.
  apply (@list_2_step_with_length_arg X P p0 px pxy l (length l) eq_refl).
Qed.

End list2_ind.




Require Import Lia.
Module list2_length.

Search (length (?a ++ ?b)). 
Theorem list_2_step_length: forall (X : Type) (P : list X -> Prop),
  P [] -> (forall x, P [x]) -> (forall x y (l : list X), P l -> P (x :: l ++ [y])) -> forall (n: nat) (l : list X), length l = n -> P l.
Proof.
  (* intros X P p0 px pxy n.
  induction n.
  - destruct l; simpl in *. auto. discriminate.
  - destruct l; auto.
    destruct (list2_func.list_back_inversion l); subst; auto.
    destruct H. destruct H. subst.
    intros.
    apply pxy.
    apply IHn. *)
  intros X P p0 px pxy n.
  apply (nat_2_step_ind (fun n => forall l, length l = n -> P l)); 
  intros; destruct l; auto.
  - simpl in *. discriminate.
  - inversion H. destruct l; auto. simpl in *. discriminate.
  - destruct (list2_func.list_back_inversion l); subst; auto.
    destruct H1. destruct H1. subst.
    apply pxy. apply H. simpl in *. rewrite app_length in *. simpl in *. lia.
Qed. 


Theorem list_2_step_inp: forall (X : Type) (P : list X -> Prop), (forall (n: nat) (l : list X), length l = n -> P l) -> (forall (l : list X), P l).
Proof.
  intros.
  destruct l.
  - eapply H. reflexivity.
  - eapply H. reflexivity.
Qed.

Theorem list_2_step: forall (X : Type) (P : list X -> Prop),
  P [] -> (forall x, P [x]) -> (forall x y (l : list X), P l -> P (x :: l ++ [y])) -> forall (l : list X), P l.
Proof.
  intros.
  apply list_2_step_inp.
  apply list_2_step_length; auto.
Qed.
Print rev_involutive.
(* found single proof which combine above three proofs *)
Theorem list_2_step_combined: forall (X : Type) (P : list X -> Prop),
  P [] -> (forall x, P [x]) -> (forall x y (l : list X), P l -> P (x :: l ++ [y])) -> forall (l : list X), P l.
Proof.
  intros X P p0 px pxy l'.

  specialize (nat_2_step_ind (fun n => forall l, length l = n -> P l)) as nat_2_step_ind.
  simpl in nat_2_step_ind.
  apply nat_2_step_ind with (length l'); 

  try reflexivity; intros; destruct l; auto. 
  - simpl in *. discriminate.
  - inversion H. destruct l; auto. simpl in *. discriminate.
  - destruct (list2_func.list_back_inversion l); subst; auto.
    destruct H1. destruct H1. subst.
    apply pxy. apply H. simpl in *. rewrite app_length in *. simpl in *. lia.
Qed.

(* here is more short proof *)
(* some parts learned from https://stackoverflow.com/questions/43011411/how-to-do-induction-differently *)
Theorem list_2_step_combined': forall (X : Type) (P : list X -> Prop),
  P [] -> (forall x, P [x]) -> (forall x y (l : list X), P l -> P (x :: l ++ [y])) -> forall (l : list X), P l.
Proof.
  intros X P p0 px pxy l.

  (* we can use this instead of above 3 lines to be short *)
  remember (length l) as n.
  generalize dependent l.
  induction n using nat_2_step_ind;
  (* TODO add "induction n using" notes *)

  intros; destruct l; auto.
  - simpl in *. discriminate.
  - inversion Heqn. destruct l; auto. simpl in *. discriminate.
  - rewrite <- (rev_involutive l) in *. destruct (rev l); auto.
    simpl in *. apply pxy. apply IHn. rewrite app_length in *. simpl in *. lia.
Qed.





End list2_length.







