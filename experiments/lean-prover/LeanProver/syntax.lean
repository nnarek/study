aimport Lean
open Lean Meta Elab Term Syntax TSyntax




def printExprTree (e : Expr) : MetaM String :=
  match e with
  | .bvar i          => pure s!"(Expr.bvar {i})"
  | .fvar fvarId     => pure s!"(Expr.fvar {fvarId.name})"
  | .mvar mvarId     => pure s!"(Expr.mvar {mvarId.name})"
  | .sort u          => pure s!"(Expr.sort {u})"
  | .const n us      => pure s!"(Expr.const {n} {us})"
  | .app f a         => do 
      let fStr ← printExprTree f
      let aStr ← printExprTree a
      pure s!"(Expr.app {fStr} {aStr})"
  | .lam n t b _     => do 
      let tStr ← printExprTree t
      let bStr ← printExprTree b
      pure s!"(Expr.lam {n} {tStr} {bStr})"
  | .forallE n t b _ => do 
      let tStr ← printExprTree t
      let bStr ← printExprTree b
      pure s!"(Expr.forallE {n} {tStr} {bStr})"
  | .letE n t v b _  => do 
      let tStr ← printExprTree t
      let vStr ← printExprTree v
      let bStr ← printExprTree b
      pure s!"(Expr.letE {n} {tStr} {vStr} {bStr})"
  | .lit l           => pure s!"(Expr.lit ({repr l}))"
  | .mdata _ e       => printExprTree e
  | .proj s i e      => do 
      let eStr ← printExprTree e
      pure s!"(Expr.proj {s} {i} {eStr})"



elab "castedExpr" : term => do
  let intType := Expr.const `Int []

  let val1 := mkRawNatLit 1
  let val2 := mkIntLit (-2)
  let val1Int ← ensureHasType intType val1

  let mul := mkMul val1Int val2

  let expr ← ensureHasType intType (← mul)
  logInfo m!"expr: {expr}"
  let pp_expr ← Lean.PrettyPrinter.ppExpr expr
  logInfo m!"ppexpr: {pp_expr}"
  return expr

#check ((((1:Nat):Int) * (-2)) : Int)
#check castedExpr   -- we do not get ((1 : Nat) * 2 : Int) because Expr does not preserve information about syntax
                    -- in this case, ensureHasType use Coe instance to pick function which casts and inject that function
                    -- but maybe we can store some metadata in Expr to preserve information about initial syntax
                    -- then I found delab interface which can be used to describe how various Exprs should be printed



#check ``Nat
#check ``Int

elab "castedSyntax" : term => do
  let val1 ← `((1 : $(mkIdent ``Nat))) -- TODO why when I use using `((1 : Nat)) then Nat remain unresolved?
  let val2 ← `(-2)
  let val1Int ← `(($val1 : $(mkIdent ``Int)))
  let mul ← `($val1Int * $val2)
  let stx ← `(($mul : $(mkIdent ``Int)))

  let ppstx := Lean.Syntax.prettyPrint stx
  let ppstxstr := Std.Format.pretty ppstx
  let term ←  Lean.PrettyPrinter.ppTerm stx
  logInfo m!"syntax: {stx}" -- prints without extra spaces
  logInfo m!"reprint syntax: {reprint stx}"
  logInfo m!"ppsyntax: {toString ppstx}"
  logInfo m!"ppsyntax str: {ppstxstr}"
  logInfo m!"ppTerm: {term}"

  let expr ← elabTermAndSynthesize stx none
  let delabExpr ← Lean.PrettyPrinter.delab expr
  dbg_trace expr

  let pp_expr ← Lean.PrettyPrinter.ppExpr expr
  logInfo m!"ppexpr: {pp_expr}"
  logInfo m!"expr: {expr}"
  logInfo m!"delabExpr: {delabExpr}"
  return expr

set_option pp.coercions.types true in
#check castedSyntax -- when we print Expr, this adds type ascription for every place where type is casted, if we cast Nat to Nat then it will not be added because Coe also not get injected in this case
-- TODO how to set this option per call of pretty printer function call?
#check castedSyntax -- without pp.coercions.types option









-- match expression is implemented via special _check.match_1 function which is automatically generated for each function and similar to inductive principle which isabelle generates for each function  
#check Nat.add.match_1
#check Nat.rec
-- this is also similar to coq
-- read more here https://proofassistants.stackexchange.com/questions/2010/how-does-lean-figure-out-that-these-variables-are-equal/2013#2013
--TODO but what is _check, I guess it is for checking defintional equality?

elab "createMatchSyntax" : term => do
  let stx ← `(match 66 with | 77 => 88 | _ => 99) -- TODO why 77 not found in the corresponding expr?
  let stx ← `(match false with | false => 88 | true => 99)
  -- dbg_trace stx

  let ppstx := Lean.Syntax.prettyPrint stx
  let term ←  Lean.PrettyPrinter.ppTerm stx
  logInfo m!"syntax: {stx}"
  logInfo m!"ppsyntax: {toString ppstx}"
  logInfo m!"ppTerm: {term}"

  let expr ← elabTermAndSynthesize stx none
  let delabExpr ← Lean.PrettyPrinter.delab expr
  dbg_trace expr 

  let expr_tree ← printExprTree expr
  logInfo m!"expr_tree: {expr_tree}" 

  let pp_expr ← Lean.PrettyPrinter.ppExpr expr
  logInfo m!"ppexpr: {pp_expr}"
  logInfo m!"delabExpr: {delabExpr}"
  return expr 

set_option pp.explicit true in
#check createMatchSyntax


--TODO use Lean.Meta.Match to create match expression


--TODO look into this
-- https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAGQKYEMB2AoUlaNWgOgBEUYUCApAZwkIDEoIQAVCa2rcaeZdAgUQA2KAEYEAQgFdggmMDQBhJiHQATTjh74CAWSRkJKKsADGG7nj56qVFAHMkGDBDBI0l90NFxmSKCDg9MjgAZRhVOCUoRwxVJAAzOAcYZgBPVzCoOAAKdwAuOAA5FBAkAEo4PIBeOFUIDDg4QX04eUTABMIk/SU0KhgASTR4iDhMRub4eGrWoYIYdMdxltVSOE6wMH4ADzAsmAa4XfkYQTQAQlrSA+iYSSh3KjOAIgBvFZgCXf15uABGAAZAUDgcCAL5PJySXooeJIWoJOAwJB9SpwfoAeVCMCg8jslSqBwA7sAYAALfpcWA6CCqSTNKhwADEAG0XiAaXS4dMAAaDEmggC6cBeoLg8ShcDcADc4FUAHy1epLeDZPpQAA0cAA+pqtRVOtlfP4vCIdAQoFCAOQ5ZJpDLYuDc4ofFCqVRagBefggZTKcwgGOF8RkSGKpXx8PiKDpME1weaOhQYAjcSjMdFL2lEeloOu+juD2xTkZSClKEEiOR+xLZYrtoWmUdzoIrvdXsYGCAA
