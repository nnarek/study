//Exercise 0. Write a method Max that takes two integer parameters and returns their maximum. Add appropriate annotations and make sure your code verifies.

method Max(a: int, b: int) returns (c: int)
  // What postcondition should go here, so that the function operates as expected?
  ensures (a == c || b == c) 
  ensures (a <= c && b <= c)

  //this one also works
  // ensures a < b ==> c==b
  // ensures a >= b ==> c==a
{
  if (a < b) {
    return b;
  } else {
    return a;
  }
}