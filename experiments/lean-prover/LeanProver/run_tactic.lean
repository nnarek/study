import Mathlib.Tactic
import Lean

open Lean Meta Elab Term Syntax TSyntax Tactic Command 


theorem your_theorem (x : Int) : x > 10 := by sorry

#check your_theorem 1

def getType {A} (_inst : A) := A

example : getType (your_theorem 11) := by simp[getType]

example : ¬ 2 > 10 := by simp

-- TODO gives unexpected result 
#eval show TermElabM Unit from do
  for x in [9 : 12] do
    let instStx ← `(your_theorem $(← exprToSyntax (mkIntLit x)))
    --let instStx ← `($(← exprToSyntax (mkIntLit x)) > 10)
    let instExpr ← elabTermAndSynthesize instStx none
    
    let instPropExpr ← Lean.Meta.inferType instExpr
    --let instPropExpr := instExpr
    let negPropExpr := mkApp (← Term.mkConst ``Not) instPropExpr

    let simpTheorems ← getSimpTheorems
    let simpTheorems ← simpTheorems.addConst `your_theorem
    let ctx ← Simp.mkContext (simpTheorems := #[simpTheorems])

    let (result, _) ← simp negPropExpr ctx
    logInfo m!"simplified : {negPropExpr} {result.expr}"
    --if result.expr.isFalse then
      --return 1
      --logInfo m!"simplified: {result.expr}"
  




#check_tactic ¬ 11 > 10 ~> False by simp
--TODO not sure how to properly detect is teorem proved or not 
-- copied from https://github.com/leanprover/lean4/blob/2104fd7da90ce810ea66949634f68c4cc1a08484/src/Lean/Elab/CheckTactic.lean#L30


def checkTacticProvesGoal' (t result tac : Syntax) : TermElabM Unit := 
    withoutModifyingEnv $ do
      let u ← withSynthesize (postpone := .no) <| Lean.Elab.Term.elabTerm t none
      let type ← inferType u
      let checkGoalType ← Lean.Meta.CheckTactic.mkCheckGoalType u type
      let mvar ← mkFreshExprMVar (.some checkGoalType)
      let expTerm ← Lean.Elab.Term.elabTerm result (.some type)
      let (goals, _) ← Lean.Elab.runTactic mvar.mvarId! tac
      match goals with
      | [] =>
        throwErrorAt t
          m!"{tac} closed goal: {t}, but is expected to reduce to {indentExpr expTerm}."
      | [next] => do
        let (val, _, _) ← Lean.Meta.CheckTactic.matchCheckGoalType t (←next.getType)
        if !(← Meta.withReducible <| isDefEq val expTerm) then
          let (val, expTerm) ← addPPExplicitToExposeDiff val expTerm
          throwErrorAt t
            m!"Term reduces to{indentExpr val}\nbut is expected to reduce to {indentExpr expTerm}"
      | _ => do
        throwErrorAt t
          m!"{tac} produced multiple goals, but is expected to reduce to {indentExpr expTerm}."


#eval show TermElabM Unit from do
  let instStx ← ``(your_theorem 11)
  let instExpr ← elabTermAndSynthesize instStx none -- withSynthesize (postpone := .no) <| Lean.Elab.Term.elabTerm instStx none --
  
  let instPropExpr ← Lean.Meta.inferType instExpr
  let negPropExpr ← `(¬ $(← exprToSyntax instPropExpr)) 
  let negPropExpr ← `(1 ≠ 2)
  dbg_trace negPropExpr
  let tacStx ← `(tactic| constructor)
  
  checkTacticProvesGoal' negPropExpr (← `(True)) tacStx





def checkTacticProvesGoal (t result tac : Syntax) : TermElabM Unit := 
    withoutModifyingEnv $ do
      let u ← withSynthesize (postpone := .no) <| Lean.Elab.Term.elabTerm t none
      let type ← inferType u
      let checkGoalType ← Lean.Meta.CheckTactic.mkCheckGoalType u type
      let mvar ← mkFreshExprMVar (.some type)
      let expTerm ← Lean.Elab.Term.elabTerm result (.some type)
      let a ← Term.runTactic mvar.mvarId! tac .term
      dbg_trace a



#eval show TermElabM Unit from do
  let instStx ← ``(your_theorem 11)
  let instExpr ← elabTermAndSynthesize instStx none -- withSynthesize (postpone := .no) <| Lean.Elab.Term.elabTerm instStx none --
  
  let instPropExpr ← Lean.Meta.inferType instExpr
  let negPropExpr ← `(¬ $(← exprToSyntax instPropExpr)) 
  let negPropExpr ← `(2 = 2)
  dbg_trace negPropExpr
  let tacStx ← `(tactic| rfl)
  let u ← withSynthesize (postpone := .no) <| Lean.Elab.Term.elabTerm negPropExpr none
  let u ← Lean.Elab.Term.elabTerm  negPropExpr (some (.sort 0))
  let mvar ← mkFreshExprMVar (.some u)
  let a ← Term.runTactic mvar.mvarId! tacStx .term (report := true)
  dbg_trace a
  dbg_trace mvar
  --checkTacticProvesGoal negPropExpr (← `(True)) tacStx





