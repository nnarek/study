import Lean
open Lean

declare_syntax_cat iaggr_sep
syntax "," : iaggr_sep
syntax ";" : iaggr_sep
syntax "." : iaggr_sep

syntax "[[" sepBy1(term,"|",iaggr_sep) "]]" : term -- here | only used to allow as to pattern match by writing $t:term|* and instead of | we also can use ,
-- note that to pattern match aginast sepBy1 and sepBy we should use * in both cases, not + for sepBy1 and * for sepBy 
-- also we can use something similar pattern 'yamlEntries $[$names:yamlIdent - $values:str]*' to pattern match aginst nested syntax at same time
-- in above case we can access array of yamlIdents by writing 'names'

--uncomment only one of macro rules
macro_rules
  -- $t have type Lean.Syntax.TSepArray and we can unwrap it by using $t,* macro
  -- | `([[ $t:term|* ]]) => `([$t,*]) 

  | `([[ $t:term|* ]]) => do 
                              let ts: Array (TSyntax `term) ← t.getElems.mapM fun
                                      | `($x:num) => `($x+1)--pure ($x |> toString |> quote)
                                      | _ => Macro.throwUnsupported
                              `([$ts,*])
  
  


#eval [[ 2 ]] 
#eval [[2; 3]] 
#eval [[2, 3]] 