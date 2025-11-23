import Mathlib.Data.Finset.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Plausible.Testable

-- import Mathlib.Tactic.SuppressCompilation can be used to make everything noncomputable

def A000006 : ℕ+ → ℤ  := sorry
def A000040  : ℕ+ → ℤ := sorry
def A000196  : ℕ → ℤ := sorry

namespace A000006 

#check #[0, 1, (2:Int64)]

-- comutable defintions get translated into C and it take lot of time to build, using noncomputable def to make compilation faster
noncomputable abbrev data : List ℤ := [1, 1, 2, 2, 3, 3, 4, 4, 4, 5, 5, 6, 6, 6, 6, 7, 7, 7, 8, 8, 8, 8, 9, 9, 9, 10, 10, 10, 10, 10, 11, 11, 11, 11, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18]
abbrev offset : Int := 1  -- offset is 1 in this case but we can not use offset in data_eq because simp tactic will not unfold it during pattern matching  

#reduce data[0]
-- #eval data[0]

#check (1:ℕ+)-(1:ℕ)
--#check getElem data (n-(1:ℕ)) (by grind)
@[simp] -- use register simp attribute to create collection of theorems related with data of sequences
theorem data_eq {n:ℕ+} {hb : n-1 < data.length}: A000006 n = data[n-(1:ℕ)] := by sorry

end A000006

namespace A000040 

abbrev data : List ℕ := [ 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271]
abbrev offset : Int := 1

@[simp] 
theorem data_eq {n:ℕ+} {hb : n-1 < data.length}: A000040 n = data[n-(1:ℕ)] := by sorry

-- for tables, define flat function inside this namespace

end A000040

namespace A000196 

abbrev data : List ℤ := [ 0, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10]
abbrev offset : Int := 0

@[simp] 
theorem data_eq {n: ℕ} {h : n-0 < data.length}: A000196 n = data[n-(0:Nat)] := by sorry

end A000196

example : A000040 1 = 2 := by simp
#check_failure A000006 0 = A000196 (A000040 0).toNat --type mismatch as expected
example : A000006 1 = A000196 (A000040 1).toNat := by simp -- do not work if A000040 return Int
example : A000006 2 = A000196 (A000040 2).toNat := by simp
example : A000006 3 = A000196 (A000040 3).toNat := by simp

def getType {A} (_inst : A) := A

-- later we will see that no need to mention that theorem works only if 1<n because type information of these function already contain it
theorem fact : A000006 n = A000196 (A000040 n).toNat := by sorry

#check_failure getType (@fact 0) -- we will get error during instantiation of this theorem

#check getType (@fact 1) -- no any error

example : getType (@fact 1) := by simp[getType]
example : getType (@fact 15) := by simp[getType]

--for sequences which starts from -2,then we can use {n : Int // -2 <= n} subtype as input type. if it starts from 2,then we can use {n : Nat // 2 <= n} subtype as input type. note that we should always use simplest built-in type of lean as base type of subtype. Also Lean support Coe for subtypes
def x : {n : Nat // 4 ≤ n} := ⟨4, by simp⟩
#check_failure x+6
#check x+(6:Nat) -- exact type of second argument should be known to pick right instance of Hadd and cast x to that type too
#check (x:Nat)+6

--if we define A000040 as ℕ+ → ℤ then 'fact' will not get typechecked and we need to also prove that result of 'A000040 n' can be casted to ℕ for any n, this will require to inject casting functions and to prove aux theorems. but there is no guaranteed way to determine result type only by looking in the data




--if we use subtypeing then in some cases correct theorems will not even get tpechecked 
def B000001 (n:{n : Nat // 4 ≤ n}) : Nat := n
def B000002 (n:{n : Nat // 6 ≤ n}) : Nat := n+1

example {n : { n // 6 ≤ n }} : (B000001 n)+1 = B000002 n := by simp[B000001,B000002]




namespace Subtype
-- detect type of argument and return type, if it is possible then it casts without losing information, otherwise it will use lowerst element of return type for non castable values of argument 
def cast {a b : Nat} (n:{n : Nat // a ≤ n}) : {n : Nat // b ≤ n} := by 
  cases' n with n _
  if hb: b ≤ n then -- will be compiled by using decidable comparison operator
    exact ⟨n,hb⟩
  else
    exact ⟨b,Nat.le_refl _⟩

end Subtype

example : (B000001 n.cast)+1 = B000002 n := by grind[B000001,B000002,Subtype.cast]
-- correct type of n automatically detected

--we can create Coe from cast function, but implicit casting is more informative for users because sometime it can be lead to lose of information
--for downcasting from Int to Nat we actually do not need to prove that it always holds. we just can convert negative integers to 0 and if theorem is valid then value of such cases will not affect to the result
--here is two main functions which we need
--https://leanprover-community.github.io/mathlib4_docs/Init/Data/Int/Basic.html#Int.toNat
--https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/PNat/Defs.html#Nat.toPNat'

universe u v
class DownCast (α : Sort u) (β : Sort v) where
  cast : α → β

attribute [grind,simp] DownCast.cast

syntax:1024 "↓" term:1024 : term
macro_rules
  | `(↓ $t) => `(DownCast.cast $t)

@[grind,simp]
instance {A: Sort u} {B: Sort v} [Coe A B] : DownCast A B where
  cast := Coe.coe

@[grind,simp]
instance {A: Sort u}  : DownCast A A where
  cast := id



--here is function which works for any kind of Props of subtypes, which should preserve information if it is possible, if not possible then it should return always same value(for example min/max value of return type)
namespace Subtype

@[grind,simp]
instance {A: Type*} {p r: A → Prop} [Inhabited {n : A // r n}] [DecidablePred r] : DownCast {n : A // p n} {n : A // r n} where
  cast := by 
            intro n
            if hrn: r n.1 then
              exact ⟨n.1,hrn⟩ 
            else
              exact default


end Subtype

instance {A: Type*} {a : A} [Preorder A] : Inhabited {n : A // a ≤ n} :=
  ⟨a, le_rfl⟩

example : (B000001 ↓n)+1 = B000002 n := by grind[B000001,B000002]


--we can add some typeclass in mathlib for such conversations, by default it will be implemented for conversations which is already implemented via Coe
--also we should implement downcast from Int to Nat, from any A:Type to Subtype of A
--we can use ↓ operator for that



open Classical

inductive A000045Impl : Nat -> Nat -> Prop
  | f0 : A000045Impl 0 1
  | f1 : A000045Impl 1 1
  | f : A000045Impl n r -> A000045Impl (n+1) r1 -> A000045Impl (n+2) (r+r1)


--I want to able to use infuctively defined function as normal function
-- to use axiom of choice we need to prove that 
theorem A000045Ex : forall n, exists r, A000045Impl n r := by 
  intro n
  match n with 
  | 0 => use 1; exact A000045Impl.f0
  | 1 => use 1; exact A000045Impl.f1
  | n+2 => match A000045Ex n,A000045Ex (n+1) with 
          | ⟨r,h⟩,⟨r1,h1⟩ => use r+r1; exact A000045Impl.f h h1


noncomputable def A000045 (n: Nat) : Nat := Classical.choose (A000045Ex n)
-- but actually if totallity of function f is not trivial to prove then it will have same complexity to prove A000045Ex because we use induction here too

--it will be good to leave empty the defintion of non trivially terminating functions, and prove facts about it by assuming that other facts are correct. but in this case we need to validate facts for many instances to make sure that it is correct. otherwise if it is false, then we can prove any other nonvalid/valid fact using it



open Lean Elab Tactic 


elab "check_goal" _name:name "[" _start:term ":" _end:term "]" tac:tactic linebreak : tactic => do
  let varName := _name.getName
  let startIt ← elabTerm _start none
  let endIt ← elabTerm _end none
  Lean.Elab.Tactic.withMainContext do
    -- let ctx ← Lean.MonadLCtx.getLCtx 
    -- dbg_trace "aa"
    -- let some varDecl := ctx.findFromUserName? name.getName | throwError "{varName} not found"
    -- let varExpr := varDecl.toExpr 

    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    let goalType := goalDecl.type
    let Expr.forallE quantVar domain body _ := goalType | throwError "Expected forall"

    if quantVar != varName then
      throwError "{varName} not found"
    --dbg_trace "{startIt}\n\n"
    let savedGoals ← getGoals
    let varType := domain
    let mut lastValidStart : Int := -9999
    let mut lastValidEnd : Int := -9998
    let mut maxValidStart : Int := lastValidStart
    let mut maxValidEnd : Int := lastValidEnd
    for n in [startIt.nat?.get! : endIt.nat?.get!+1] do
      try
        let arg ← if varType.isConstOf `Nat then `($(Syntax.mkNatLit n)) else `(↓ $(Syntax.mkNatLit n))
        let argExpr ← elabTerm arg varType
        --let startType ← Lean.Meta.inferType argExpr 
        --dbg_trace "startExpr: {argExpr}\n\n"
        Lean.Meta.check argExpr

        let instantiated := body.instantiate1 argExpr --(mkNatLit 1)-
        --dbg_trace "goal type for n={n}: {← Lean.PrettyPrinter.ppExpr instantiated}\n"

        let mvar ← Meta.mkFreshExprMVar instantiated
        let tempGoal := mvar.mvarId!  

        setGoals [tempGoal]

        evalTactic tac
        --dbg_trace "✓ Base case n={n} is decidable and true\n"
        if lastValidEnd + 1 = n then
          lastValidEnd := n
        else
          lastValidStart := n
          lastValidEnd := n
        

        --setGoals savedGoals
      catch e => 
        if (maxValidEnd - maxValidStart + 1) < (lastValidEnd - lastValidStart + 1) then
          maxValidStart := lastValidStart
          maxValidEnd := lastValidEnd
        continue

    if (maxValidEnd - maxValidStart + 1) < (lastValidEnd - lastValidStart + 1) then
      maxValidStart := lastValidStart
      maxValidEnd := lastValidEnd

    dbg_trace "check_goal `{_name.getName} [{maxValidStart},{maxValidEnd}] [{0},{0}]" --second range is soundness
    setGoals savedGoals

  -- Lean.Elab.Tactic.withMainContext do
  --   let ctx ← Lean.MonadLCtx.getLCtx 
  --   let decls := (ctx.decls.toArray.filterMap id)--.filter (fun decl => decl.userName = name.getName)

  --   decls.forM fun 
  --     decl => do
  --       --if decl.kind != LocalDeclKind.auxDecl then  -- theorem itsels also added as local decl, we noly need assumptions  
  --         let declExpr := decl.toExpr 
  --         let declName := decl.userName 
  --         let declType ← Lean.Meta.inferType declExpr 
  --         dbg_trace f!"+ local decl: name: {declName} | expr: {declExpr} | type: {declType}\n"  


instance {A: Sort u} {p: A → Prop} [Inhabited {n : A // p n}] [DecidablePred p] : DownCast A {n : A // p n}  where
  cast := by 
            intro n
            if hrn: p n then
              exact ⟨n,hrn⟩ 
            else
              exact default


#eval (↓↓1 : Nat) --TODO

example : B000001 ↓(↓1 : { n // 6 ≤ n }) + 1 = B000002 (↓1 : { n // 6 ≤ n }) := by decide
 
example : let n : { n // 6 ≤ n } := ↓1; B000001 ↓n + 1 = B000002 n := by decide

theorem temp : ∀ n, (B000001 ↓n)+1 = B000002 n := by 
  check_goal `n [0:80] (decide) --TODO shoudld report maximal satisfiable range, in this case it is 6,80
  
  sorry --plausible


--TODO check_goal should create new goal if there is other quantified variables and tactics not able to prove them automatically
--so we can apply check_goal again on other quantified variables too
theorem tempa : ∀ n, ( n <= 10 ) → False := by 
  check_goal `n [6:101] (decide)--TODO should report valid range(6,101) and soundness range(11,101)
  --check_goal `n [11, 99]
  sorry
  
  

open Plausible
#test ∀ n, n + 1 = 1 + n
--#test ∀ n, (B000001 n.cast')+1 = B000002 n









theorem real_thm : (1.2 : ℝ) < (1.3 : ℝ) * (1.3 : ℝ) := by
  --native_decide
  --ring
  norm_num -- casts finite real numbers into ℚ and then use normalization tactics of nat numbers
#print real_thm


theorem real_thm' : (1.2 : ℝ) < Real.pi := by
  --norm_num
  --native_decide
  --ring

  sorry