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

