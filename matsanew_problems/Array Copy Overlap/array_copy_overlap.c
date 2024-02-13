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
  if (d < s)
  {
    // Forward copy
    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall int k; 0 <= k < i ==> d[k] == s[k];
      loop assigns i, d[0..n-1];
      loop variant n - i;
     */
    for (int i = 0; i < n; i++)
    {
      d[i] = s[i];
    }
  }
  else
  {
    // Backward copy for overlap handling
    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall int k; 0 <= k < i ==> d[n-k-1] == s[n-k-1];
      loop assigns i, d[0..n-1];
      loop variant i;
     */
    for (int i = n; i > 0; i--)
    {
      d[i - 1] = s[i - 1];
    }
  }
}