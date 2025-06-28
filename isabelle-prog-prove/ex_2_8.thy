theory ex_2_8
  imports Main
begin

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []" |
"intersperse a (h#t) = h#a#(intersperse a t)"

theorem map_intersperse: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs)
  apply(auto)
  done                              

end