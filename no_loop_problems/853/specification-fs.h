/* Star */

/*@
    requires \valid(out);
    requires 1 <= a <= 18257;
    assigns *out;
    behavior a_is_1:
        assumes a == 1;
        ensures *out == 1;
    behavior a_is_not_1:
        assumes a != 1;
        ensures *out == 6 * (a - 1) * a + 1;
*/
void star(int a, int *out);