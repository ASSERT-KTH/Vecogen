typedef unsigned int uint;

/*@
  predicate is_common_divisor(uint d, uint a, uint b) = a % d == 0 && b % d == 0;

  lemma order_a_b:
    \forall uint a, b, d; is_common_divisor(d, a, b) <==> is_common_divisor(d, b, a);

  lemma divides_itself:
    \forall uint a; a > 0 ==> is_common_divisor(a, a, a);

  axiomatic axm {
    axiom subtraction:
      \forall uint a, b, d; a >= b ==>
      (is_common_divisor(d, a, b) <==> is_common_divisor(d, a - b, b));
  }
 */

/*@
  requires A > 0 && B > 0;
  assigns \nothing;
  ensures is_common_divisor(\result, A, B);
  ensures \forall uint d; is_common_divisor(d, A, B) ==> d <= \result;
*/
uint euclid(uint A, uint B)
{
    /*@
      loop invariant A > 0 && B > 0;
      loop invariant \forall uint d; is_common_divisor(d, \at(A, Pre), \at(B, Pre)) ==> is_common_divisor(d, A, B);
      loop assigns A, B;
      loop variant A + B;
    */
    while (A != B)
    {
        if (A > B)
        {
            A = A - B;
        }
        else
        {
            B = B - A;
        }
    }
    return A;
}
