#include <stdbool.h>

/*You are tasked with determining whether two integers have opposite signs. 
	The integers can be positive, negative, or zero, and you need to assess their signs to conclude if one is positive while the other is negative.

	Input
	The function takes two integer parameters, a and b. Each integer can range from -2,147,483,648 to 2,147,483,647.

	Output
	The function returns a boolean value: true if the integers have opposite signs, and false otherwise.
*/

/*@
requires \true;
  assigns \nothing;
  ensures \result <==> ((a < 0 && b > 0) || (a > 0 && b < 0));
@
*/

bool HasOppositeSign(int a, int b) {
    return (a < 0 && b > 0) || (a > 0 && b < 0);
}
