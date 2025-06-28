theory ex_3_5
  imports Main
begin

datatype alpha = a | b  

(* we can imagine two languages and each of them have only '(' and ')' characters  *)
(* S language have empty word,allow to enclose word inside (), allow to concat two words  *)
(* T language have empty word,allow to concat two words after enclosing second word inside ()  *)

inductive S :: "alpha list ⇒ bool" where
S_e : "S []" |
S_aSb : "S w ==> S (a # w @ [b])" |
S_SS : "S w1 ==> S w2 ==> S (w1 @ w2)"

inductive T :: "alpha list ⇒ bool" where
T_e  : "T []" |
T_TaTb : "T w1 ==> T w2 ==> T (w1 @ (a # w2 @ [b]))"  (*T (w1 @ (a # w2 @ [b]))"*)

thm T.induct

lemma T_aTb: "T w ⟹ T (a # w @ [b])"
  using T_TaTb T_e by fastforce


  
  

lemma T_concat: "T w1 ⟹ T w2 ⟹ T (w1 @ w2)"
  apply(induction w1 arbitrary: w2 rule: T.induct)
   apply simp
  sorry
  (*TODO unfinidhed *)


theorem S_imp_T: "S w ==> T w"
  apply(induction w rule: S.induct)
    apply(auto intro: T.intros)
    apply(auto intro: T_concat)
    using T_TaTb T_e by fastforce
    

theorem T_imp_S: "T w ==> S w"
  apply(induction w rule: T.induct)
   apply(auto intro: S.intros)
  done

theorem S_eq_T: "S w = T w" (*for bool, equality is same as equivalence*)
  apply(auto intro: S_imp_T T_imp_S)
  done
  

end