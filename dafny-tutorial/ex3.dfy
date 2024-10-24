//Exercise 3. Keeping the postconditions of Abs the same as above, change the body of Abs to just y := x + 2. What precondition do you need to annotate the method with in order for the verification to go through? What precondition do you need if the body is y := x + 1? What does that precondition say about when you can call the method?

method Abs(x: int) returns (y: int)
  // Add a precondition here so that the method verifies.
  requires x == -1//y==x never will be satisfiable and y==-x will be satisfiable only when x==-1

  // Don't change the postconditions.
  ensures 0 <= y
  ensures 0 <= x ==> y == x
  ensures x < 0 ==> y == -x
{
  y:= x + 2;
}
method Abs2(x: int) returns (y: int)
  // Add a precondition here so that the method verifies.
  requires false//means that posconditions never can be satisfiable, so function never can be called (we also can write x==0 && x==1 or any other statement which is always false)

  // Don't change the postconditions.
  ensures 0 <= y
  ensures 0 <= x ==> y == x
  ensures x < 0 ==> y == -x
{
  y:= x + 1;
}