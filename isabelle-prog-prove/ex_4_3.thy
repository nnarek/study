theory ex_4_3
  imports Main
begin

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"




lemma assumes a: "ev(Suc(Suc n))" shows "ev n"
proof - 
  from a show "ev n" 
  proof cases
    case ev0
    then show "ev n" using assms ev.cases by blast
  next
    (*there is only one goal after destruction of "a" *)
  qed
qed


end