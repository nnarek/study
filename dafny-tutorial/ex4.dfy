//Exercise 4. Write a function max that returns the larger of two given integer parameters. Write a test method using an assert that checks that your function is correct.

function max(a: int, b: int): int
{
  if a < b then b else a
}
method Testing() {
  assert max(4,5)==5;
}