/*The function calculates the greatest common divisors (GCD). The greatest common divisor of two or more integers is the largest positive integer that divides each of the integers without leaving a remainder. The GCD is calculated using a recursive implementation of the Euclidean algorithm, a well-known method for finding the GCD of two numbers.

   The goal of this task is to compute the greatest common divisor (GCD) of two given numbers, 'a' and 'b'. The function 'gcd_rec' receives two non-negative integers and returns their greatest common divisor. The function must ensure that the result is indeed the GCD of the input numbers, following the mathematical definition that a number 'd' is the GCD of 'a' and 'b' if it divides both 'a' and 'b' and no larger number has this property.

   Input
   The input to the function 'gcd_rec' are two non-negative integers 'a' and 'b'. 

   Output
   The output of the function 'gcd_rec' is a single integer which is the greatest common divisor of the input numbers 'a' and 'b'. The function ensures that the returned result is indeed the GCD of 'a' and 'b' by adhering to the mathematical definition of GCD.
*/

/*@
inductive is_gcd(integer a, integer b, integer d) {
      case gcd_zero:
         \forall integer n; is_gcd(n,0,n);
      case gcd_succ:
         \forall integer a,b,d; is_gcd(b, a % b, d) ==> is_gcd(a,b,d);
   }
*/

/*@
axiomatic gcd {
      logic integer gcd(integer a, integer b);

      axiom nil:
         \forall integer n; gcd(n,0) == n;
      axiom next:
         \forall integer a,b; gcd(b, a % b) == gcd(a,b);
   }
*/

/*@
decreases b;
   assigns \nothing;
   ensures is_gcd(a, b, \result);
   ensures \result == gcd(a, b);
*/

unsigned gcd_rec(unsigned a, unsigned b) {
   if (b == 0) {
      return a;
   }
   return gcd_rec(b, a % b);
}
