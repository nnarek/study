theory ex_4_6
  imports Main
begin

fun elems :: "'a list => 'a set" where
"elems [] = {}" |
"elems (h#t) = {h} Un (elems t)"





lemma "x ∈ elems xs ==> ∃ ys zs. xs = ys @ x # zs ∧ x ∉ elems ys"
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case using elems.simps by (metis append.left_neutral append_Cons empty_iff insertE
      insert_is_Un)
qed


end