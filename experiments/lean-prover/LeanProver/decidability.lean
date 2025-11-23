inductive Numb
  | zero 
  | succ (a: Numb)
  deriving DecidableEq -- automatically generates function which checks equality between Numb instances 

#check DecidableEq Numb

#eval Decidable.decide (Numb.zero = (Numb.succ Numb.zero))
#eval Decidable.decide ((Numb.succ Numb.zero) = (Numb.succ Numb.zero)) 

-- TODO try to create inductive type which equality is undecidable, if such inductive type exists

-- try to find code of default handler of DecidableEq class

example : Decidable.decide (Numb.zero = (Numb.succ Numb.zero)) = false := by
  unfold decide instDecidableEqNumb
  simp[*]
  decide

#check instDecidableEqNumb ?a ?b
#reduce instDecidableEqNumb ?a ?b
#check Numb.rec

def instDecidableEqNumb' (a b : Numb) : Decidable (a = b) :=
  match a,b with 
  |Numb.zero , Numb.zero => isTrue rfl
  |Numb.zero , Numb.succ _ => isFalse (by simp)
  |Numb.succ _,Numb.zero => isFalse (by simp)
  |Numb.succ a,Numb.succ b => by simp; exact instDecidableEqNumb' a b 

def instDecidableEqNumb_eqZero (a : Numb) : Decidable (a = Numb.zero) := @Numb.rec 

def instDecidableEqNumb'' (a : Numb) : (b : Numb) → Decidable (a = b) := @Numb.rec 
                                                                            (fun b => Decidable (a = b)) 
                                                                            (by simp; )  

--TODO try to write default handler for inductive relations(with exact two parameters), which is not possible in general, but we can automatically decide in most cases 