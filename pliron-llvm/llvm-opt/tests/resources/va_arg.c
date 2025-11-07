#include <stdarg.h>
#include <stdio.h>

// Function to calculate the sum of a variable number of integers
int sum_variadic_args(int count, ...) {
  int sum = 0;
  va_list args; // Declare a va_list object

  // Initialize va_list to point to the first variadic argument
  va_start(args, count);

  // Iterate through the variadic arguments and add them to the sum
  for (int i = 0; i < count; i++) {
    sum += va_arg(args, int); // Retrieve the next argument as an int
  }

  // Clean up the va_list object
  va_end(args);

  return sum;
}

int main() {
  // Example usage
  int total1 = sum_variadic_args(3, 10, 20, 30);

  int total2 = sum_variadic_args(5, 1, 2, 3, 4, 5);

  return total1 + total2;
}
