theory ex_2_6
  imports Main
begin

datatype 'a tree = None | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents None = []" |
"contents (Node lt x rt) = x # ((contents lt) @ (contents rt))"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree None = 0" |
"sum_tree (Node lt x rt) = x + (sum_tree lt + sum_tree rt)"

theorem sum_eq: "sum_tree t = sum_list (contents t)"
  apply(induction t)
  apply(auto)
  done
                                                   