/*@
axiomatic power_function {
    axiom power_zero: \forall integer n; n == 0 ==> (long) \pow(1378, n) % 10 == 1;
    axiom power_mod_one: \forall integer n; n % 4 == 1 ==> (long) \pow(1378, n) % 10 == 8;
    axiom power_mod_two: \forall integer n; n % 4 == 2 ==> (long) \pow(1378, n) % 10 == 4;
    axiom power_mod_three: \forall integer n; n % 4 == 3 ==> (long) \pow(1378, n) % 10 == 2;
    axiom power_mod_zero: \forall integer n; n % 4 == 0 && n != 0 ==> (long) \pow(1378, n) % 10 == 6;
  }
*/

/*@
requires 0 <= n <= 1000000000;
    assigns \nothing;
    ensures \result == (long) \pow(1378, n) % 10;
*/

