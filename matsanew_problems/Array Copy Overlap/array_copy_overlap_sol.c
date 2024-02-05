/* Method copy() copies n chars from source array s[] to destination array d[];
   the two arrays (of n elements each) are allowed to overlap.
   Note that the implementation uses a pointer-comparison (d < s) which is
   undefined in the C language.
 */

/*@
  requires n >= 0;
  requires \valid(d + (0..n-1)) && \valid(s + (0..n-1));
  assigns d[0..n-1];
  ensures \forall int i; 0 <= i <= n-1 ==> d[i] == \old(s[i]);
 */
void copy(char d[], char s[], int n)
{
    int i;

    if (d == s || n == 0)
        return;

    if (d < s)
    {
        /* Either d[] and s[] do not overlap, or the overlap is after some chars
           of d[]. Copy in forward direction. */

        i = 0;

        /*@
          loop assigns d[0..n-1], i;
          loop invariant 0 <= i <= n;
          loop invariant \forall int j; 0 <= j <= i-1 ==> d[j] == \at(s[j], Pre);

          // Total i chars written in d[], and upto i-1 chars written at the beginning
          // of s[] due to possible overlap.
          loop invariant \forall int j; i-1 <= j <= n-1 ==> s[j] == \at(s[j], Pre);
          loop variant n-i;
         */
        while (i < n)
        {
            d[i] = s[i];
            i = i + 1;
        }
    }
    else
    {
        /* d > s */
        /* Either d[] and s[] do not overlap, or the overlap is after some chars
           of s[]. Copy in backward direction. */

        i = n - 1;

        /*@
          loop assigns d[0..n-1], i;
          loop invariant -1 <= i <= n-1;
          loop invariant \forall int j; i+1 <= j <= n-1 ==> d[j] == \at(s[j], Pre);

          // Total n-1-i chars written in d[], and upto n-2-i chars written at the end
          // of s[] due to possible overlap.
          loop invariant \forall int j; 0 <= j <= i+1 ==> s[j] == \at(s[j], Pre);
          loop variant i+1;
         */
        while (i >= 0)
        {
            d[i] = s[i];
            i = i - 1;
        }
    }
}