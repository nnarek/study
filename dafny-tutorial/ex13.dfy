//Exercise 13. Change the definition of sorted so that it allows its argument to be null (using a nullable array type) but returns false if it is.

predicate sorted(a: array<int>) // Change the type
  reads a
{
  // Change this definition to treat null arrays as "not sorted".
  // (i.e. return false for null arrays)
  forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}