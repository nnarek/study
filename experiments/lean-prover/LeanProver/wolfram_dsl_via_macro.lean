

declare_syntax_cat wexpr
syntax ident : wexpr -- idents is specifal tokens denoting variables
syntax num : wexpr  
syntax str : wexpr  -- str is string literals
syntax "(" wexpr ")" : wexpr  
syntax "Wl[" wexpr "]" : term -- auxiliary notation for translating wolfram expressions into lean terms, maybe use WL[ ] naming?
syntax "Lean[" term "]" : wexpr  -- this syntax allow to use lean terms inside DSL, maybe we need to use Lean naming?
syntax:60 wexpr:60 "+" wexpr:61 : wexpr  
syntax:70 wexpr:70 "*" wexpr:71 : wexpr  

-- TODO maybe use wexpr,+ or wexpr,* which also will include empty args  
declare_syntax_cat wargs
syntax wexpr : wargs
syntax wexpr "," wargs : wargs


macro_rules
  | `(Wl[ $x:ident]) => `($x)
  | `(Wl[ $numt:num ]) => `($numt)
  | `(Wl[ $x + $y ]) => `(Wl[ $x ] + Wl[ $y ])
  | `(Wl[ $x * $y ]) => `(Wl[ $x ] * Wl[ $y ])
  | `(Wl[ ($x) ]) => `(Wl[ $x]) -- means that top parentheses can be reduced
  | `(Wl[ Lean[ $e:term ]]) => pure e

-- built-in functions of wolfram
declare_syntax_cat wlist
syntax "List[" "]" : wlist
syntax "List[" wargs "]" : wlist
syntax wlist :wexpr
macro_rules
  | `(Wl[ List[ ] ]) => `([])
  | `(Wl[ List[ $x:wexpr ] ]) => `([ Wl[ $x:wexpr] ])
  | `(Wl[ List[ $x:wexpr, $a:wargs ] ]) => `(Wl[ $x ] :: Wl[ List[ $a ] ])
#check Wl[List[]]  
#check Wl[List[2,3]]  
#check Wl[List[2,3,5]]  


/-
class TimesDef (α : Type u) where
  times : α → α

instance : TimesDef Nat where
  times := fun a  => a 

def times_rec (l : List Nat) : Nat 
  | List.nil => 1
  | h :: t => h * times_rec t

instance : TimesDef (List α) where
  times := 
-/

syntax "Times[" "]" : wexpr
syntax "Times[" wargs "]" : wexpr
macro_rules
  | `(Wl[ Times[ ] ]) => `(1)
  | `(Wl[ Times[ List[ $a:wargs ] ] ]) => `(Wl[ Times[ $a ] ])
  | `(Wl[ Times[ $x:wexpr ] ]) => `(Wl[ $x:wexpr ]) -- more general case should be after the more specific case
  | `(Wl[ Times[ $x:wexpr, $a:wargs ] ]) => `(Wl[ $x ] * Wl[ Times[ $a ] ])
#check Wl[Times[]]  
#check Wl[Times[2,3]]  
#check Wl[Times[2,3,5]]  





syntax "Set[" wargs "]" : wexpr

--syntax "CompoundExpression[" "]" : wexpr
syntax "CompoundExpression[" wargs "]" : wexpr
macro_rules
--  | `(Wl[ CompoundExpression[ ] ]) => `( )
  | `(Wl[ CompoundExpression[ $x:wexpr ] ]) => `(Wl[ $x:wexpr ])
  | `(Wl[ CompoundExpression[ Set[$x:ident,$e:wexpr ], $b:wargs ] ]) => `(let $x := Wl[$e] ; Wl[CompoundExpression[ $b ] ])
--#check Wl[CompoundExpression[]]  
#check Wl[CompoundExpression[Set[a,List[2,3]],Times[a]]]  -- wrong matched, 'a' is just indent and hence it is wexpr, so will be match with Times[wexpr]
#check Wl[CompoundExpression[Set[a,1],Set[b,2],Times[a,b]]]  

--TODO to solve above issue first try to define one polymprphic times function in lean and map macro to only it 


#check_failure Wl[x]  
#check Wl[ 2 * 1]  
#check Wl[ 1 + 9 ]   
#check Wl[ 5 + 7 *6]   
#check Wl[ (1 + 8) * Lean[3.1]]  

#eval Wl[ 1 + 9 ] 


def xPlusY := Wl[ 2 + 9]
#print xPlusY  

#check Wl[ Lean[ xPlusY] + 4]  
