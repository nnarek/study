theory ex_2_4
  imports Main
begin

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] x = [x]" |
"snoc (h#t) x = h#(snoc t x)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (h#t) = snoc (reverse t) h"

lemma rev_snoc[simp]: "reverse (snoc xs a) = a # (reverse xs)"
  apply(induction xs)
  apply(auto)
  done

theorem rev_rev: "reverse (reverse xs) = xs"
  apply(induction xs)
  apply(auto)
  done
