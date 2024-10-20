//Exercise 1. Write a test method that calls your Max method from Exercise 0 and then asserts something about the result.

include "ex0.dfy"

method Testing() {
  // Assert some things about Max. Does it operate as you expect?
  // If it does not, can you think of a way to fix it?
  var m := Max(0,2);
  assert m == 2;

  var m1 := Max(1,1);
  assert m1 == 1;
}