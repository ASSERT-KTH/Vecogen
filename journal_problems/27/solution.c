/*
  In a mathematical context, an Armstrong number (also known as a narcissistic number) 
  for a three-digit number is one whose sum of the cubes of its digits is equal to the 
  number itself. The task is to determine whether a given three-digit integer meets this 
  criterion.

  Input
  The input is an integer n, where n is guaranteed to be within the range of 100 to 999, inclusive.

  Output
  The output is a boolean value indicating whether the input number n is an Armstrong number. 
  It will return true if n is an Armstrong number, and false otherwise.
*/
#include <stdbool.h>

/*@
  requires 100 <= n && n < 1000;
  assigns \nothing;
  ensures \result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)));
@*/
bool IsArmstrong(int n) {
    int a = n / 100;
    int b = (n / 10) % 10;
    int c = n % 10;
    return n == (a * a * a + b * b * b + c * c * c);
}