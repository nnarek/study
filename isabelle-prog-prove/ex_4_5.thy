theory ex_4_5
  imports Main
begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl : "star r x x" |
step : "r y z ==> star r x y ==> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
irefl : "r x x \<Longrightarrow> iter r 0 x x" |
istep : "iter r n x y ==> r y z ==> iter r (Suc n) x z"


lemma "iter r n x y ==> star r x y"
proof -
  show "iter r n x y \<Longrightarrow> star r x y" 
  proof (induction rule: iter.induct)
    case (irefl x)
    then show ?case by (metis refl)
  next
    case (istep n x y z)
    then show ?case by (metis step)
  qed
qed

end