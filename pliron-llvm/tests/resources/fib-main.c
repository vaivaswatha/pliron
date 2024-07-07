#include <stdio.h>

extern int fib(int n);

int main() {

  printf("fib(0): %d\n", fib(0));
  printf("fib(1): %d\n", fib(1));
  printf("fib(2): %d\n", fib(2));
  printf("fib(3): %d\n", fib(3));
  printf("fib(4): %d\n", fib(4));

  return 0;
}
