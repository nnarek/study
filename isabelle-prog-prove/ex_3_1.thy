theory ex_3_1
  imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree ⇒ 'a set" where
"set Tip = {}" |
"set (Node l a r) = (set l) Un {a} Un (set r)"

fun ord :: "int tree ⇒ bool" where 
"ord Tip = True" |
"ord (Node l a r) = ((case l of Tip ⇒ True | Node ll la lr ⇒ la < a) \<and>
                    (case r of Tip ⇒ True | Node rl ra rr ⇒ a < ra))"

fun ins :: "int ⇒ int tree ⇒ int tree" where
"ins x Tip = Node Tip x Tip" |
"ins x (Node l a r) = (if a=x then 
                          (Node l a r) 
                      else if x<a then
                          Node (ins x l) a r
                      else 
                          Node l a (ins x r))"

theorem tree_set_ins: "set (ins x t) = {x} Un set t"
  apply(induction t)
  apply(auto)
  done

theorem tree_set_ord: "ord t ==> ord (ins i t)"
  apply(induction t arbitrary: i)
  apply(auto split: tree.split)
  done

end