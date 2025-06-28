theory ex_4_7
  imports Main
begin

datatype alpha = a | b  

inductive S :: "alpha list ⇒ bool" where
S_e : "S []" |
S_aSb : "S w ==> S (a # w @ [b])" |
S_SS : "S w1 ==> S w2 ==> S (w1 @ w2)"

inductive T :: "alpha list ⇒ bool" where
T_e  : "T []" |
T_TaTb : "T w1 ==> T w2 ==> T (w1 @ (a # w2 @ [b]))"  

fun balanced :: "nat ⇒ alpha list ⇒ bool" where
"balanced 0 [] = True" |
"balanced (Suc n) [] = False" |
"balanced 0 (h#t) = (if h = b then False else balanced 1 t)" |
"balanced (Suc n) (h#t) = (if h = b then balanced n t else balanced (Suc (Suc n)) t)"

lemma "balanced n w = S (replicate n a @ w)"
proof 
  show "balanced n w ⟹ S (replicate n a @ w)"
  sorry
(*TODO unfinished *)
end