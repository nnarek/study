

Definition get_withness(e: exists n, n = 0) : nat.
Proof.
    Fail destruct e. (* match expression and any other computation against Propositions like "exists" not allowed if function return nat,bool or other sets *)
    apply 0.
Qed.

Definition destruct_withness(e: exists n, n = 0) : 0=0.
Proof.
    destruct e. (* match expression and any other computation against Propositions liek "exists" not allowed if function return other proposition like "0=0",but in here match expression or other computation will not be performed, because Props have no computational meaning in Coq and Coq will only type check this function *)
    auto.
Qed.

Print destruct_withness.

(* sigma is not defined as Prop and it is defined as Type, so we can get withness from it *)
Definition get_withness_sigma(e: {n : nat | n = 0}) : nat.
Proof.
    destruct e.
    exact x.
Qed.

Print sig.
Print get_withness_sigma.



(* TODO how get withness from exists by using axiom of choice like we do in Lean? *)