/*@
    requires \valid(out);
    requires 1 <=  x <= 1000000;
    assigns *out;
    ensures *out == (x + 4) / 5;
*/
void calculateMinimumElephantSteps(int x, int *out);