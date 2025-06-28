theory ex_3_4
  imports Main
begin

inductive star :: "('a ⇒ 'a ⇒ bool) ⇒ 'a ⇒ 'a ⇒ bool" for r where
refl : "star r x x" |
step : "r y z ==> star r x y ==> star r x z"

inductive iter :: "('a ⇒ 'a ⇒ bool) ⇒ nat ⇒ 'a ⇒ 'a ⇒ bool" for r where
irefl : "iter r 0 x x" |
istep : "iter r n x y ==> r y z ==> iter r (Suc n) x z"


theorem star_imp_iter: "star r x y ==> ∃n. iter r n x y"
  apply(induction rule: star.induct)
   apply(metis irefl)
   apply(metis istep)
  done

theorem iter_imp_star: "iter r n x y ==> star r x y"
  apply(induction rule: iter.induct)
   apply(metis refl)
   apply(metis step)
  done

end