From Coq Require Export Arith.
Require Import Program.Wf.
Require Import Coq.Program.Tactics.
Require Import Coq.Init.Wf.



(* coq does not allow to create custom kinds/universes like Prop  *)
Axiom MyKind : Type. 
Axiom MyType1 : MyKind.
Fail Axiom MyInctance : MyType1.





Theorem lem_irrefusable : forall  (P : Prop), ~~(P \/ ~P).
Proof.
  unfold not.
  intros P H.
  apply H.
  right.
  intros.
  apply H.
  left.
  assumption.
Qed.

Theorem double_negation_excluded_middle : ~~(forall (P : Prop), P \/ ~P).
Proof.
Admitted.

Theorem lem_irrefusable' :  ~~(forall  (P : Prop), P \/ ~P).
Proof.

  unfold not.
  intros H.
  apply H.
  intros.
  right.
  intros.
  apply H.
  intros.
  right.
  intros.
  apply H.
Abort.

Theorem func_extensionality_irrefusable : forall  (A B: Type) (f g: A -> B), ~~(forall (x: A), f x = g x -> f = g ).
Proof.
  unfold not.
  intros A B f g H.
  apply H.
  intros. 
Abort.








Definition lem := (forall Q: Prop, Q \/ ~Q).
Definition wem := (forall Q: Prop, ~Q \/ ~~Q).


Search (~(?P /\ ?Q)).
Search (~?P /\ ~~?P).
(* demorgan law for negation of disjunction is evivalent to lem but demorgan law for negation of conjuction is not equivalent *)
Lemma demorgan_neg_conj_eqv_wem :
  (forall P Q: Prop, ~(P /\ Q) -> ~P \/ ~Q) <-> wem.
Proof.
  unfold wem.
  split; intros.
  - apply H. intros Hl. destruct Hl. auto.  
  - destruct (H P); auto. right. intros q. apply H1. intros p. apply H0. split; auto. 
Qed.

(* wem is not equivalent to lem and if we can prove "wem->lem <-> lem" then it will mean that we can not prove that wem<->lem *)
Lemma wem_neqv_lem :
  (wem -> lem) <-> lem.
Proof.
  unfold wem,lem.
  split.
  - intros H.
    apply H.
    intros.
    apply H.
Abort.

Lemma wem_neqv_lem :
  ((forall P: Prop, ~P \/ ~~P -> P \/ ~P)) <-> lem.
Proof.
  unfold lem.
  split.
  - intros.
    apply H.
    apply H.
    apply H.
Abort.








(* seems like this one also have its own category *)
Definition not_exists_dist := forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).


Theorem lem_impl_not_exists_dist :
  lem ->
  not_exists_dist.
Proof.
  unfold lem,not_exists_dist.
  intros lem X P Hne x.
  destruct (lem (P x)); auto.
  exfalso. apply Hne. exists x. assumption.
Qed.


(* if we can prove this then it will mean that no_exists_dist is not equivalent to lem because in that case we can prove wem -> lem which is not true *)
Theorem wem_imp_not_exists_dist :
  wem -> not_exists_dist.
Proof.
  unfold wem, not_exists_dist.
  intros wem X P Hne x.
  destruct (wem (P x)).
  - exfalso. apply Hne. exists x. assumption.
  - admit.
Abort.




Lemma not_exists_dist_imp_lem : 
  not_exists_dist -> lem.
Proof.
  unfold lem, not_exists_dist.
  intros Hne_im_f.
  apply Hne_im_f.
  intros e.
  destruct e.
  apply H.
  right.
  eapply Hne_im_f.
  intros Hf.
  destruct Hf.
  (* left.
  intros p.
  assert (Hnf : ~ (forall P : Prop, P)).
  + intros Hf.  *)
Abort.

Theorem wem_imp_not_exists_dist :
  not_exists_dist -> wem.
Proof.
  unfold wem, not_exists_dist.
  intros not_exists_dist Q.
  left.
  apply not_exists_dist.
  intros He.
  destruct He. 

Abort.






Definition not_forall_dist := forall (X:Type) (P : X -> Prop),
    ~ (forall x, P x) -> (exists x, ~ P x).

Theorem not_forall_dist_proof : not_forall_dist.
Proof.
  unfold not_forall_dist.
  intros.
  eexists.
  intros Hf.
  apply H.
  intros.
Abort.

Theorem lem_imp_not_forall_dist : lem -> not_forall_dist.
Proof.
  unfold not_forall_dist.
  intros Hlem X P H.
  destruct (Hlem (exists x : X, ~ P x)); auto.
  exfalso.
  apply H.
  apply (lem_impl_not_exists_dist Hlem). 
  assumption.
Qed.


Theorem wem_imp_not_forall_dist : wem -> not_forall_dist.
Proof.
  unfold not_forall_dist.
  intros Hwem X P H.
  destruct (Hwem (~forall x : X, P x)); auto.
  - exfalso. auto.
  - admit.
Abort.


Theorem not_forall_dist_imp_lem : not_forall_dist -> lem.
Proof.
  unfold not_forall_dist,lem.
  intros.
Abort.

Theorem aa : not_forall_dist <-> not_exists_dist.
Proof.
  unfold not_forall_dist,not_exists_dist.
  split; intros.
  - Fail apply H.
Abort.


Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P Hf [x HnP].
  apply HnP.
  apply Hf.
Qed.

Theorem dist_not_exists' : forall (X:Type) (P : X -> Prop),
  (forall x, ~ P x) -> ~ (exists x, P x).
Proof.
  intros X P Hf [x HP].
  apply (Hf x HP).
Qed.

Theorem aafd : not_forall_dist -> forall (X:Type) (P : X -> Prop),
    ~ (forall x, ~ P x) -> (exists x, P x).
Proof.
  intros.
  Fail apply H.
Abort.


