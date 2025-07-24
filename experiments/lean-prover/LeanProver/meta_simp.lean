import Lean

open Lean Meta

#eval show MetaM Unit from do
  let x ← mkFreshExprMVar (mkConst ``Nat)
  let zero := mkConst ``Nat.zero
  let expr := mkAppN (mkConst ``Nat.add) #[zero, mkAppN (mkConst ``Nat.add) #[x, zero]]
  
  let simpTheorems ← getSimpTheorems
  let ctx ← Simp.mkContext (simpTheorems := #[simpTheorems])

  let (result, _) ← simp expr ctx
  logInfo m!"original: {expr}"
  logInfo m!"simplified: {result.expr}"

