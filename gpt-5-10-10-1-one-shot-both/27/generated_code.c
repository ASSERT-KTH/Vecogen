#include <stdbool.h>

/*In a mathematical context, an Armstrong number (also known as a narcissistic number) 
  for a three-digit number is one whose sum of the cubes of its digits is equal to the 
  number itself. The task is to determine whether a given three-digit integer meets this 
  criterion.

  Input
  The input is an integer n, where n is guaranteed to be within the range of 100 to 999, inclusive.

  Output
  The output is a boolean value indicating whether the input number n is an Armstrong number. 
  It will return true if n is an Armstrong number, and false otherwise.
*/

/*@
requires 100 <= n && n < 1000;
  assigns \nothing;
  ensures \result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)));
@
*/

bool IsArmstrong(int n) {
    int d1 = n / 100;
    int d2 = (n / 10) % 10;
    int d3 = n % 10;
    int sum = d1 * d1 * d1 + d2 * d2 * d2 + d3 * d3 * d3;
    return n == sum;
}
