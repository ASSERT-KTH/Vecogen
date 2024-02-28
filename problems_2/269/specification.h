/*  Pythagorean Triples
    Katya studies in a fifth grade. Recently her class studied right triangles and the Pythagorean theorem. It appeared, that there are triples of positive integers such that you can construct a right triangle with segments of lengths corresponding to triple. Such triples are called Pythagorean triples . For example, triples (3, 4, 5) , (5, 12, 13) and (6, 8, 10) are Pythagorean triples. Here Katya wondered if she can specify the length of some side of right triangle and find any Pythagorean triple corresponding to such length?
*/

/*@
    requires \valid(out_1) && \valid(out_2) && \valid(out_3) && separated(out_1, out_2, out_3);
    requires \valid(a) && \valid(b) && \valid(c);
    requires
    assigns *out;
    ensures
*/
void problem(int a, int b, int c, int *out);

#define ll                                                                                                                                  \
    long long int int main()                                                                                                                \
    {                                                                                                                                       \
        ll n, a;                                                                                                                            \
        scanf("%lld", &n);                                                                                                                  \
        (n < 3) ? printf("-1") : printf("%lld %lld", (n % 2 == 0) ? n *n / 4 - 1 : n *n / 2, (n % 2 == 0) ? n * n / 4 + 1 : n * n / 2 + 1); \
    }
