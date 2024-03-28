/*
    Katya studies in a fifth grade. Recently her class studied right triangles and the Pythagorean theorem. It appeared, that there are triples of positive integers such that you can construct a right triangle with segments of lengths corresponding to triple. Such triples are called Pythagorean triples . For example, triples (3, 4, 5) , (5, 12, 13) and (6, 8, 10) are Pythagorean triples. Here Katya wondered if she can specify the length of some side of right triangle and find any Pythagorean triple corresponding to such length?
*/

/*@
    requires \valid(out1) && \valid(out2) && \separated(out1, out2);
    requires 1 <= N <= 1000000000;
    assigns *out1, *out2;
    behavior N_less_than_3:
        assumes N < 3;
        ensures *out1 == -1 && *out2 == -1;
    behavior N_greater_than_3_and_N_odd:
        assumes N >= 3 && N % 2 != 0;
        ensures *out1 == (N * N - 1) / 2 && *out2 == (N * N  + 1) / 2;
    behavior N_greater_than_3_and_N_even:
        assumes N >= 3 && N % 2 == 0;
        ensures *out1 == (N * N) / 4 - 1 && *out2 == (N * N) / 4 + 1 ;
    complete behaviors;
    disjoint behaviors;
*/
void findPythagoreanTripleForSide(int N, long *out1, long *out2)
{
    long n = N;
    if (n < 3)
    {
        *out1 = -1;
        *out2 = -1;
    }
    else
    {
        if (n % 2 != 0)
        {
            *out1 = (n * n - 1) / 2;
            *out2 = (n * n + 1) / 2;
        }
        else
        {
            *out1 = (n * n) / 4 - 1;
            *out2 = (n * n) / 4 + 1;
        }
    }
}
