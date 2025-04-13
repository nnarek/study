theory ex_3_2
  imports Main
begin

inductive palindrome :: "'a list => bool" where
p0: "palindrome []" |
ps: "palindrome xs ==> palindrome (a # xs @ [a])"

thm palindrome.induct (*TODO what is intuition behind this?*)

theorem palindrome_rev: "palindrome xs ==> rev xs = xs"
  apply(induction xs rule: palindrome.induct)
  apply(auto)
  done

end