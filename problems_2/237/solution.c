
/*@
    requires \valid(out);
    requires 1 <= N <= 1000000000;
    assigns *out;
    ensures *out == ((N + 1) / 2);
*/
void problem(int N, int *out)
{
    if (N % 2 == 0)
        *out = (N / 2);
    else
        *out = (N / 2) + 1;
}