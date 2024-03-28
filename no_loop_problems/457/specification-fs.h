/*@
    requires \valid(out);
    requires 1 <= n <= 25;
    assigns *out;
    behavior n_11_to_19_or_21:
        assumes n >= 11 && n <= 19 || n == 21;
        ensures *out == 4;
    behavior n_20:
        assumes n == 20;
        ensures *out == 15;
    behavior n_other:
        assumes n != 20 && !(n >= 11 && n <= 19 || n == 21);
        ensures *out == 0;
    complete behaviors;
    disjoint behaviors;
*/
void calculateWaysToGetSecondCardForBlackjack(int n, int *out);