/* Star  */

/*@
    requires 1 <= a <= 18257;
    \assigns \nothing;
    behavior a_is_1:
        assumes a == 1;
        ensures \result == 1;
    behavior a_is_not_1:
        assumes a != 1;
        ensures \result == 6 * (a - 1) * a + 1;
*/
int problem(int a);