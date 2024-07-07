int fib(int n) {
  if (n == 1) {
    return 0;
  }
  if (n == 2) {
    return 1;
  }

  int prev2 = 0;
  int prev1 = 1;

  int cur;
  for (int i = 3; i <= n; i++) {
    cur = prev1 + prev2;
    prev2 = prev1;
    prev1 = cur;
  }
  return cur;
}
