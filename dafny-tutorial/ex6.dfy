//Exercise 6. Change the loop invariant to 0 <= i <= n+2. Does the loop still verify? Does the assertion i == n after the loop still verify?

method m(n: nat)
{
  var i: int := 0;
  while i < n
    invariant 0 <= i <= n + 2 
  {
    i := i + 1;
  }

  //at the end, dafny will know that
  //0 <= i <= n+2
  //n <= i
  //and we can not conclude that i == n because it can be n+1 or n+2
  
  //assert i == n;

  assert n <= i && i <= n + 2;
}