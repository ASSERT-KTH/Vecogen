#include <stddef.h>

/*@ predicate SameContents{L1, L2}(char* a, integer b, integer e) =
  \forall integer i; b <= i < e ==> \at(a[i], L1) == \at(a[i], L2);
*/

/*@
  requires n >= 0;
  requires \valid(d + (0..n-1)) && \valid(s + (0..n-1));
  assigns d[0..n-1];
  ensures SameContents{Pre, Here}(s, 0, n) && SameContents{Pre, Here}(d, 0, n);
*/
void copy(char* d, char* s, int n) {
    int i = 0;

    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer j; 0 <= j < i ==> d[j] == s[j];
      loop assigns i, d[0..n-1];
      loop variant n - i;
    */
    while (i < n) {
        // Assertion to verify element copying in each iteration
        //@ assert d[i] == s[i];

        d[i] = s[i];
        ++i;
    }
    
    // Assertion to verify final contents after loop
    //@ assert SameContents{Here, Here}(s, 0, n) && SameContents{Here, Here}(d, 0, n);
}
