//Exercise 5. Now that we have an abs function, change the postcondition of method Abs to make use of abs. After confirming the method still verifies, change the body of Abs to also use abs. (After doing this, you will realize there is not much point in having a method that does exactly the same thing as a function.)

function method abs(x: int): int
{
  if x < 0 then -x else x
}
method Abs(x: int) returns (y: int)
  ensures y==abs(x)
{
  return abs(x);
}