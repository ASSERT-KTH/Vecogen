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
void copy(char d[], char s[], int n);