(* 
Record Peano_theory : Type :=
  { nt : Type
  ; znt : nt
  ; snt : nt -> nt
  ; nt_NEQ : forall n: nt, znt <> snt n
  ; nt_INV : forall n: nt, n = znt \/ exists n', n = snt n'
  ; nt_INJ : forall n m: nt, snt n = snt m -> n = m
  ; (* other axioms here *)
  }.

Theorem Peano_theory_provable : Peano_theory.
Proof.
  refine {| nt := nat ; znt := 0 ; snt := S |}.
  - intros n H.
    inversion H.
  - intros.
    destruct n; auto.
    right. eexists. auto.
  - intros. 
    inversion H. auto.
    Show Proof. (* here I saw that nt_inj and nt_new can be proved by by eq_ind and nat_inv*)
Qed.

Print f_equal.
Print eq_ind_r.

Theorem Peano_theory_irrefutable : ~~ inhabited Peano_theory.
Proof.
  intros H; apply H; constructor; apply Peano_theory_provable.
Qed. *)

Axiom nt : Type.
Axiom znt : nt.
Axiom snt : nt -> nt.

Definition nt_neq := forall n: nt, znt <> snt n.
Definition nt_inv := forall n: nt, n = znt \/ exists n', n = snt n'.
Definition nt_inj := forall n m: nt, snt n = snt m -> n = m.
Definition nt_ind :=  forall P : nt -> Prop, 
                      P znt -> 
                      (forall n : nt, P n -> P (snt n)) -> 
                                  forall n : nt, P n.
(* here we assume that axioms of equality, but later we can add them into set of axioms too *)

(* above axioms are sufficient to prove that "n <> snt n" *)
Theorem n_neq_sntn : nt_neq -> nt_inj -> nt_ind -> forall n: nt, n <> snt n.
Proof.
  intros nt_neq nt_inj nt_ind n.
  apply (nt_ind (fun n => n <> snt n)).
  - apply nt_neq.
  - intros. intros H'. apply H. apply (nt_inj _ _ H').
  Show Proof.
Qed.


Theorem and_irr_implies_irr_and : forall (A B : Prop),  ~~A /\ ~~B -> ~~(A /\ B).
Proof.
  intros A B [nnA nnB].
  intros nAB.
  apply nnA.
  intros a.
  apply nnB.
  intros b.
  apply nAB.
  split; auto.
Qed.


Theorem nt_neq_irr : ~~nt_neq.
Proof.
  unfold nt_neq.
  intros H.
  apply H.
  intros n eq.
  apply H.
Abort.

Theorem nt_inv_irr : ~~nt_inv.
Proof.
  unfold nt_inv.
  intros H.
  apply H.
  intros.
Abort.



(* seems like we can not prove them one by one
try to prove all of them at once *)

Theorem nt_irr : ~~(nt_neq /\ nt_inv /\ nt_ind).
Proof.
  unfold nt_neq,nt_inv,nt_inj,nt_ind.
  intros Hni.
  apply Hni.
  split.
  - intros n Heq.
    apply Hni.
    split.
Abort.

Theorem nt_irr_neq : forall n: nt, ~~(znt <> snt n).
Proof.
  unfold not.
  intros n Hn.
  apply Hn.
  intros H.
  
Abort.


Theorem nt_irr_eqiv : forall (P : nt -> Prop), ~~(forall (n: nt), P n) <->  (forall (n: nt), ~~(P n)).
Proof.
  intros.
  split.
Abort.