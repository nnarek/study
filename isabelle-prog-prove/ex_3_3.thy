theory ex_3_3
  imports Main
begin

inductive star' :: "('a ⇒ 'a ⇒ bool) ⇒ 'a ⇒ 'a ⇒ bool" for r where
refl' : "star' r x x" |
step' : "star' r x y ==> r y z ==> star' r x z"

inductive star :: "('a ⇒ 'a ⇒ bool) ⇒ 'a ⇒ 'a ⇒ bool" for r where
refl : "star r x x" |
step : "r y z ==> star r x y ==> star r x z"


theorem star'_imp_star: "star' r x y ==> star r x y"
  apply(induction rule: star'.induct)
   apply(rule refl)
   apply(auto dest: step) (*or we can use apply(metis step)*) 
  done

theorem star_imp_star': "star r x y ==> star' r x y"
  apply(induction rule: star.induct)
   apply(auto intro: star'.intros)
  done

end