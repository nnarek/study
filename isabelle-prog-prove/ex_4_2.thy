theory ex_4_2
  imports Main
begin

lemma "∃ ys zs. xs = ys @ zs ∧ (length ys = length zs ∨ length ys = length zs + 1)"
proof
  let ?y = "take ((length xs+1) div 2) xs" 
  let ?z = "drop ((length xs+1) div 2) xs"
  show "∃ zs. xs = ?y @ zs ∧ (length ?y = length zs ∨ length ?y = length zs + 1)" (*I can not refine two variables at once*)
  proof
    show "xs = ?y @ ?z ∧ (length ?y = length ?z ∨ length ?y = length ?z + 1)" by auto
  qed
qed


(*TODO find short way of proof
lemma my_lemma: "∃x y :: nat. x + y = 5 ∧ x > 0"
proof (rule exI[where x = 2])
  show "∃y. 2 + y = 5 ∧ 0 < 2" 
  proof (rule exI[where y = 3])
  qed
qed
*)
end