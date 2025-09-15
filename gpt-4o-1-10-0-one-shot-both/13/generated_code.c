#include <limits.h>

/*The problem involves calculating the factorial of a non-negative integer. 
	The goal is to implement a function that can compute this value accurately while adhering to specific constraints regarding the input.

	Input
	The input consists of a single integer variable, n. 
	This integer must be non-negative (0 or greater) and should be such that its factorial does not exceed the maximum value representable by an integer in C.

	Output
	The output is a single integer, which is the factorial of the input value n. 
	The output will always be greater than or equal to 1, reflecting the properties of factorial computation.
*/

/*@
logic integer fact_log(integer n) = 
    (n == 0 ? 1 : n * fact_log(n - 1));
*/

/*@
requires 0 <= n;
    requires fact_log(n) < INT_MAX;
    decreases n;
    assigns \nothing;
    ensures \result == fact_log(n);
    ensures \result >= 1;
*/

int factorial(int n) {
    if (n == 0) {
        return 1;
    } else {
        return n * factorial(n - 1);
    }
}
