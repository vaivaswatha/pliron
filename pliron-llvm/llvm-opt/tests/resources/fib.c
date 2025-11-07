#include <stdio.h>

int fib(int n) {
  if (n <= 1) {
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

int main() {
  printf("fib(0): %d\n", fib(0));
  printf("fib(1): %d\n", fib(1));
  printf("fib(2): %d\n", fib(2));
  printf("fib(3): %d\n", fib(3));
  printf("fib(4): %d\n", fib(4));
  return 0;
}
