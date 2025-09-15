/*@
axiomatic power_function {
    axiom ending_power_five: \forall integer n; n >= 2 ==> (long) \pow(5, n) % 100 == 25;
  }
*/

/*@
requires 2 <= n <= 2 * 1000000000000000000;
    assigns \nothing;
    ensures \result % 100 == (long) \pow(5, n) % 100;
*/

