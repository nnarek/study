import Lean
open Lean Meta Elab Term

inductive ArithExpr where
| nat : Nat → ArithExpr
| int : Int → ArithExpr
| mul : ArithExpr → ArithExpr → ArithExpr

namespace ArithExpr

def toExpr : ArithExpr → MetaM Lean.Expr
| nat val => return mkNatLit val
| int val   => return mkIntLit val
| mul a b => return ← mkMul (← toExpr a) (← toExpr b)

end ArithExpr

open ArithExpr

elab "ToExpr[" t:term "]" : term => do
  let expr ← elabTermAndSynthesize t (some (.const ``ArithExpr []))
  let arithExpr ← unsafe evalExpr ArithExpr (.const ``ArithExpr []) expr
  arithExpr.toExpr

#check ToExpr[ mul (int 2) (int (3+1)) ] -- output:  2 * 4 : Int
#check_failure fun x:Int ↦ ToExpr[ mul (int 2) (int (3+x)) ] -- open terms can not be evaluated