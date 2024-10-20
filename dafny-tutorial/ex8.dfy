//Exercise 8. The ComputeFib method above is more complicated than necessary. Write a simpler program by not introducing a as the Fibonacci number that precedes b, but instead introducing a variable c that succeeds b. Verify your program is correct according to the mathematical definition of Fibonacci.

function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}
method ComputeFib(n: nat) returns (b: nat)
  ensures b == fib(n)  // Do not change this postcondition
{
  if n == 0 { return 0; }
  var i: int := 1;
  b := 1;
  var c := 1;
  while i < n
    invariant 0 < i <= n
    invariant c == fib(i + 1)
    invariant b == fib(i)
  {
    b, c := c, b + c;
    i := i + 1;
  }
}