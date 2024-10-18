//Exercise 10. In the loop above, the invariant i <= n and the negation of the loop guard allow us to conclude i == n after the loop (as we checked previously with an assert. Note that if the loop guard were instead written as i != n (as in Exercise 7), then the negation of the guard immediately gives i == n after the loop, regardless of the loop invariant. Change the loop guard to i != n and delete the invariant annotation. Does the program verify? What happened?

method m()
{
  var i, n := 0, 20;
  while i != n
    decreases n - i
  {
    i := i + 1;
  }
}