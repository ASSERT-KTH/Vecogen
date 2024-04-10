/*
    Katya studies in a fifth grade. Recently her class studied right triangles and the Pythagorean theorem. It appeared, that there are triples of positive integers such that you can construct a right triangle with segments of lengths corresponding to triple. Such triples are called Pythagorean triples . For example, triples (3, 4, 5) , (5, 12, 13) and (6, 8, 10) are Pythagorean triples. Here Katya wondered if she can specify the length of some side of right triangle and find any Pythagorean triple corresponding to such length?
*/

/*@ predicate TripleExists(long N) =
    \exists long x, y;
    1 <= x <= 1000000000000000000 &&
    1 <= y <= 1000000000000000000 &&
    (x * x + y * y == N * N || x * x + N * N == y * y || N * N + y * y == x * x);
 */

/*@
    requires \valid(out1) && \valid(out2) && \separated(out1, out2);
    requires N == 2 ;
    assigns *out1, *out2;
    ensures 1 <= *out1 <= 1000000000000000000 || *out1 == -1;
    ensures 1 <= *out2 <= 1000000000000000000 || *out2 == -1;
    behavior no_triple:
        assumes !TripleExists(N);
        ensures *out1 == -1;
        ensures *out2 == -1;
    behavior triple:
        assumes TripleExists(N);
        ensures (   *out1 * *out1 + *out2 * *out2 == N * N ||
                    *out1 * *out1 + N * N == *out2 * *out2 ||
                    N * N + *out2 * *out2 == *out1 * *out1);
    disjoint behaviors;
    complete behaviors;

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
