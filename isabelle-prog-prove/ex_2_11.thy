theory ex_2_11
  imports Main
begin

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp ⇒ int ⇒ int" where
"eval Var x = x" |
"eval (Const e) x = e" |
"eval (Add a b) x = (eval a x)+(eval b x)" |
"eval (Mult a b) x = (eval a x)*(eval b x)"

fun evalp :: "int list ⇒ int ⇒ int" where
"evalp [] x = 0" |
"evalp (h#t) x = h + x*(evalp t x)"

fun addp :: "int list ⇒ int list ⇒ int list" where
"addp xs [] = xs" |
"addp [] xs = xs" |
"addp (h1#t1) (h2#t2) = (h1+h2)#(addp t1 t2)"

fun multnp :: "int ⇒ int list ⇒ int list" where
"multnp e [] = []" |
"multnp e (h#t) = (h*e)#(multnp e t)"

(* (h1+x*t1)*(h2+x*t2)=h1*h2+h1*x*t2+h2*x*t1+x*x*t1*t2 *)
fun multp :: "int list ⇒ int list ⇒ int list" where
"multp [] xs = []" |
"multp xs [] = []" |
"multp (h1#t1) (h2#t2) = addp ((h1*h2)#0#(multp t1 t2)) 
                              (0#(addp (multnp h1 t2) (multnp h2 t1)))"

fun coeffs :: "exp ⇒ int list" where
"coeffs Var = [0,1]" |
"coeffs (Const n) = [n]" |
"coeffs (Add a b) = addp (coeffs a) (coeffs b)" |
"coeffs (Mult a b) = multp (coeffs a) (coeffs b)"

thm addp.induct

theorem evalp_addp_dist[simp]: "evalp (addp p1 p2) x = evalp p1 x + evalp p2 x"
  apply(induction p1 p2 rule: addp.induct)
  apply(auto)
  apply(simp add:algebra_simps)
  done

thm multnp.induct

theorem evalp_multnp[simp]: "evalp (multnp h1 t2) x = h1 * evalp t2 x"
  apply(induction h1 t2 rule: multnp.induct) (*or apply(induction t2 arbitrary: h1 x)*) 
  apply(auto)
  apply(simp add:algebra_simps)
  done

theorem evalp_multp_dist[simp]: "evalp (multp p1 p2) x = evalp p1 x * evalp p2 x"
  apply(induction rule: multp.induct)
  apply(auto)
  apply(simp add:algebra_simps)
  done

theorem eval_preserve: "evalp (coeffs e) x = eval e x"
  apply(induction e arbitrary: x)
  apply(auto)
  done

end