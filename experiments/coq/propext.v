Require Import Coq.Logic.PropExtensionality.


Print propositional_extensionality.
Print proof_irrelevance.
(* trying to prove that this axiom is incompatible with coq*)

Inductive POr : Prop :=
| C1
| C2.

Theorem c1_neq_c2 : C1 <> C2.
Proof.
  intro h.
  inversion h.
  (* Inductive Props have no axiom that constructors are different *)
Fail Qed.
Abort.

Theorem POr_neq_True : POr <> True.
Proof.
  intro h.
  inversion h.
Fail Qed.
Abort.



