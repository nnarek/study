theory ex_2_3
  imports Main
begin

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x [] = 0" | 
"count x (h#t) = (if x=h then 1 else 0)+(count x t)"

theorem count_less: "count x xs \<le> length xs"
  apply(induction xs)
  apply(auto)
  done

end