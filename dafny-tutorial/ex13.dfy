//Exercise 13. Change the definition of sorted so that it allows its argument to be null (using a nullable array type) but returns false if it is.

predicate sorted(a: array?<int>) 
  reads a
{
  if a==null then 
    false 
  else 
    forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}