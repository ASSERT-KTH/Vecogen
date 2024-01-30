/*@ requires n > 0;
requires \valid(p+ (0..n−1));
assigns \nothing;
ensures \forall int i; 0 <= i <= n−1 ==> \result >= p[i];
ensures \exists int e; 0 <= e <= n−1 && \result == p[e];
*/
int max_seq(int *p, int n);
