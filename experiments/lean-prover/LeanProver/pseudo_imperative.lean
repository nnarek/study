import Mathlib.Data.List.Basic


def containsFive (xs : List Nat) : Bool := Id.run do
  for x in xs do
    if x == 5 then 
      return true
  return false

#eval containsFive [1,5]

example : containsFive [1,5] = true := by simp only [containsFive]; simp


-- generates: (do let r ← forIn xs 0 fun x r => do pure PUnit.unit pure (ForInStep.yield (r + x)) pure r).run
-- but existing simplification theorems able to simplify it to the (List.foldl (fun b a => b + a) 0 xs)
def sum_loop (xs : List Nat) : Nat := Id.run do
  let mut res := 0
  for x in xs do
    res := res + x
  return res

example : sum_loop xs = List.sum xs := by simp[sum_loop, List.sum]; simp [List.foldl_eq_foldr] 

-- generates: (forIn a 0 fun x r => if x = 0 then pure (ForInStep.yield (x + 1)) else pure (ForInStep.yield r)).run
def num_0s (xs : List Nat) : Nat := Id.run do
  let mut res := 0
  for x in xs do
    if x = 0 then 
      res := res + 1
  return res

#eval num_0s  [1,2,0,0]

example : num_0s xs = List.foldl (fun b a => if a = 0 then b+1 else b) 0 xs := by 
  simp [num_0s]
  set fn1 := (fun b a => _)
  set fn2 := (fun b a => _) 
  generalize 0 = init_val
  induction' xs with h t generalizing init_val 
  · simp
  · simp
    cases' h
    · simp[*,fn1,fn2] 
    · simp[*,fn1,fn2] 



def two_loop_sum (xs : List Nat) : Nat := Id.run do
  let mut sum := 0
  for x in xs do
    for y in xs do
      sum := sum + x + y
  return sum


example : two_loop_sum xs = 2 * xs.sum * xs.length := by
  induction' xs with h t
  · simp[two_loop_sum]
  · simp[two_loop_sum]; sorry