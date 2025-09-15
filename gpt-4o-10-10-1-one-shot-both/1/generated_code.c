#include <limits.h>

/*The context of this problem is a mathematical situation involving the computation of the discriminant value in a quadratic equation. The discriminant is the part of the quadratic formula under the square root (b^2 - 4ac) and it determines the number of solutions a quadratic equation has. The code checks if the discriminant is greater than or equal to zero or less than zero. 

  The goal of this program is to check the discriminant of a given quadratic equation, and return either 0 or 1 based on the value of the discriminant. If the discriminant is greater than or equal to zero, the program will return 0 indicating that the quadratic equation has real roots. On the other hand, if the discriminant is less than zero, the program will return 1 indicating that the quadratic equation has complex roots.

  Input
  The input to the function is three integers a, b, and c, representing the coefficients of a quadratic equation of the form ax^2 + bx + c = 0.

  Output
  The output of the function is an integer. The function returns 0 if the discriminant of the quadratic equation is greater than or equal to zero, and returns 1 if the discriminant is less than zero.
*/

/*@
requires INT_MIN  <= a <= INT_MAX;
  requires INT_MIN  <= b <= INT_MAX;
  requires INT_MIN  <= c <= INT_MAX;
  requires LLONG_MIN <= 1LL*b*b <= LLONG_MAX;
  requires LLONG_MIN <= 4LL*a*c <= LLONG_MAX;
  assigns \nothing;
  ensures \result == ((1LL*b*b - 4LL*a*c) < 0);
*/

int check(int a, int b, int c) {
    long long b_squared = 1LL * b * b;
    long long a_c_product = 4LL * a * c;
    return (b_squared < a_c_product);
}
