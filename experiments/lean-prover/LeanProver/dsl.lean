import Lean
open Lean Meta

inductive ExprTree where
  | const (n : Nat)
  | add (left : ExprTree) (right : ExprTree)
  | mul (left : ExprTree) (right : ExprTree)

namespace ExprTree

#check HAdd.hAdd 1 2
#check @HAdd.hAdd Nat Nat Nat _ 1 2
#check @HAdd.hAdd Nat Nat Nat (@instHAdd Nat (@instAddNat)) 1 2

meta def toExpr : ExprTree → MetaM Expr
  | const n    => return mkNatLit n
  -- mkAppN f #[a₀, ..., aₙ] is same as "f a₀ a₁ ... aₙ"

  -- look into Lean/Meta/AppBuilder.lean if want to see how to create Expr for other operators 
  | add t1 t2  => return ← mkAdd (← toExpr t1) (← toExpr t2)
  | mul t1 t2  => return ← mkMul (← toExpr t1) (← toExpr t2)

end ExprTree

-- represents (2 * 3) + (4 * 5)
def testExpr : ExprTree := 
  .add (.mul (.const 2) (.const 3))
       (.mul (.const 4) (.const 5))

#check ExprTree.toExpr testExpr

#eval show MetaM Unit from do
  let expr ← ExprTree.toExpr testExpr
  logInfo m!"Expression: {expr}" -- output: 2 * 3 + 4 * 5

  let typeExpr ← Lean.Meta.inferType expr
  logInfo m!"Type of Expr: {typeExpr}" -- output: Nat

  let normal_form ← whnf expr
  logInfo m!"Normal form: {normal_form}" -- output: 26

  let pp_expr ← Lean.PrettyPrinter.ppExpr expr
  logInfo m!"Pretty printed Expr: {pp_expr}" -- output: 2 * 3 + 4 * 5

  let reduced ← reduce expr
  logInfo m!"Reduced: {reduced}" -- output: 26

meta unsafe def compute_expr_tree (tree : ExprTree) : MetaM Nat := do
  let expr ← ExprTree.toExpr tree
  let typeExpr ← Lean.Meta.inferType expr
  evalExpr' Nat ``Nat expr

def testTree : ExprTree :=
  .add (.mul (.const 2) (.const 3))
       (.mul (.const 4) (.const 5))

#eval show MetaM Unit from do
  let evalExpr ← compute_expr_tree testTree
  logInfo m!"Evaluated: {evalExpr}" -- output: 26
