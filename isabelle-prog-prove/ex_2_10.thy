theory ex_2_10
  imports Main
begin

datatype tree0 = None | Node "tree0" "tree0"

fun nodes :: "tree0 ⇒ nat" where 
"nodes None = 1" |
"nodes (Node l r) = (nodes l) + (nodes r)"

fun explode :: "nat ⇒ tree0 ⇒ tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"


theorem node_count: "nodes (explode n t) = (2^n)*(nodes t)"
  apply(induction n arbitrary: t)
  apply(simp)
  done