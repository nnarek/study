theory ex_2_2
  imports Main
begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add m 0 = m" |
"add m (Suc n) = Suc(add m n)"

theorem add_assoc: "add a (add b c) = add (add a b) c"
  apply(induction c)
  apply(auto)
  done

lemma add_zero[simp]: "add 0 b = b"
  apply(induction b)
  apply(auto)
  done

lemma add_succ[simp]: "add (Suc a) b = Suc (add a b)"
  apply(induction b)
  apply(auto)
  done

theorem add_comm: "add a b = add b a"
  apply(induction a)
  apply(auto)
  done

end

