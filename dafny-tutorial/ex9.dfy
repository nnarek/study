//Exercise 9. Starting with the completed ComputeFib method above, delete the if statement and initialize i to 0, a to 1, and b to 0. Verify this new program by adjusting the loop invariants to match the new behavior.

function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}
method ComputeFib(n: nat) returns (b: nat)
  ensures b == fib(n)
{
  var i: int := 0;
  var a := 1;
  b := 0;
  while i < n
    invariant 0 <= i <= n
    invariant a == fib(i + 1)
    invariant b == fib(i)
  {
    a, b := a + b, a;
    i := i + 1;
  }
}