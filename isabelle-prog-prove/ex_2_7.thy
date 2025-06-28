theory ex_2_7
  imports Main
begin

datatype 'a tree = None | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror None = None" |
"mirror (Node l x r) = Node (mirror r) x (mirror l)"

fun pre_order :: "'a tree \<Rightarrow> 'a list" where
"pre_order None = []" |
"pre_order (Node l x r) = x # ((pre_order l) @ (pre_order r))"

fun post_order :: "'a tree \<Rightarrow> 'a list" where
"post_order None = []" |
"post_order (Node l x r) = (post_order l) @ (post_order r) @ [x]"

theorem pre_post_order: "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
  apply(auto)
  done

end