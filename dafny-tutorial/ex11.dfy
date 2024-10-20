//Exercise 11. Write a method that takes an integer array, which it requires to have at least one element, and returns an index to the maximum of the array’s elements. Annotate the method with pre- and postconditions that state the intent of the method, and annotate its body with loop invariant to verify it.

method FindMax(a: array<int>) returns (i: int)
  requires 0 < a.Length 
  ensures 0 <= i < a.Length 
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
{
  i := 0;
  var index: int := 1; 
  while index != a.Length 
    invariant 1 <= index <= a.Length 
    invariant 0 <= i < index
    invariant forall k :: 0 <= k < index ==> a[k] <= a[i]
  {
    if a[i] < a[index] {
      i := index;
    } 
    index := index + 1;
  }
}