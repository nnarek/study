import Smt

def aa : Σ' x: Nat, x + 1 = 9 := by smt -- says that, cannot translate fun x => x + 1 = 9, SMT-LIB does not support lambdas

#eval aa.fst
