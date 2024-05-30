/*@
    requires 1 <= M <= N <= 16
    requires \valid(out)
    assigns *out
    ensures *out ==  M * N / 2
*/
void amountOfDominosFit(int M, int N, int *out);