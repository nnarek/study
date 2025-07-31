open Nat

-- first I was thinking that using axiom of chioce can lead to the contradiction if we will define noncomputable function which specification have few solutions
-- but it is not true, because axiom of chioce choose some of solutions but we can not determine which one it is
-- if there is few solutions then we can prove theorem about solution returned by axiom of choice only if other solutions also satisfy to that theorem
-- so we can derive properties which is derivable from specification
-- also we can derive some new properties by knowing that there exists function which always return one of solutions(and return always same thing), but existance of such function do not allow us to prove properties which is specific to only one of solutions 


namespace exp1

def NatSolutionSubType : Type := {x : Nat // x * 0 = 0 && x < 1}

theorem exists_solution : Nonempty NatSolutionSubType := ⟨⟨0, rfl⟩⟩

noncomputable def solution : Nat :=
  (Classical.choice exists_solution).val

theorem solution_spec : solution * 0 = 0 && solution < 1 := by
  exact (Classical.choice exists_solution).property

theorem solution_eq_0 : solution = 0 := by
  have h := solution_spec
  simp at h
  exact h

end exp1


namespace exp2

def NatSolutionSubType : Type := {x : Nat // x * 0 = 0}

theorem exists_solution : Nonempty NatSolutionSubType := ⟨⟨0, rfl⟩⟩

noncomputable def solution : Nat :=
  (Classical.choice exists_solution).val

theorem solution_spec : solution * 0 = 0 := by
  exact (Classical.choice exists_solution).property

theorem solution_eq_0 : solution = 0 := by
  have h := solution_spec
  
  sorry -- stuck here, assumptions are not sufficient to prove it

end exp2
