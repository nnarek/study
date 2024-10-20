//Exercise 7. With the original loop invariant, change the loop guard from i < n to i != n. Do the loop and the assertion after the loop still verify? Why or why not?

method m(n: nat)
{
  var i: int := 0;
  while i != n
    invariant 0 <= i <= n
  {
    i := i + 1;
  }

  //at the end dafny will know that
  //0 <= i <= n
  //n == i
  //which is satisfiable only if i==n
  assert i == n;
}