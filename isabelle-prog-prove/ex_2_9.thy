theory ex_2_9
  imports Main
begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 y = y" |
"add (Suc x) y = Suc (add x y)"

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 y = y" |
"itadd (Suc x) y = itadd x (Suc y)"

lemma add_succ[simp]: "add a (Suc b) = Suc (add a b)"
  apply(induction a)
  apply(auto)
  done

theorem itadd_add : "itadd x y = add x y"
  apply(induction x arbitrary: y)
  apply(auto)
  done                              