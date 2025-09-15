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

