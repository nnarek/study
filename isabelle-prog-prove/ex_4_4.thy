theory ex_4_4
  imports Main
begin

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"




lemma "\<not> ev (Suc (Suc (Suc 0)))" (* is "?h \<Longrightarrow> False" *) (*TODO how to pattern match*)
proof
  assume h: "ev (Suc (Suc (Suc 0)))"
  from h show False
  proof cases
    case ev0
    then show "?thesis" using ev.cases h by auto
  qed
qed


end