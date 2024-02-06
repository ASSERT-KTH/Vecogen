/* Method euclid() computes the greatest-common-divisor (GCD) of positive
   integers A and B, using the Euclid's GCD algorithm. The variant of the
   algorithm below reduces 'a' (similarly 'b') to (a-b). There is another
   variant which reduces 'a' to the remainder (a mod b). */

typedef unsigned int uint;

/*@
  // is 'd' a common-divisor of 'a' and 'b' ?
  predicate is_common_divisor(uint d, uint a, uint b) =
    a%d == 0 && b%d == 0;

  lemma order_a_b:
    \forall uint a, b, d; is_common_divisor(d, a, b) <==> is_common_divisor(d, b, a);

  lemma divides_itself:
    \forall uint a; a > 0 ==> is_common_divisor(a, a, a);

  axiomatic axm {
    axiom subtraction:
      \forall uint a, b, d; a > b ==>
      (is_common_divisor(d, a, b) <==> is_common_divisor(d, (uint)(a-b), b));
  }
 */

/*@
  requires A > 0 && B > 0;
  assigns \nothing;
  ensures is_common_divisor(\result, A, B);

  // the result is the greatest among all common-divisors of A and B
  ensures \forall uint d; is_common_divisor(d, A, B) ==> d <= \result;
*/
uint euclid(uint A, uint B);