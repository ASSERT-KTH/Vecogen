/*@
requires a != \null && b != \null;
  requires len > 0;
  requires \valid(a + (0 .. len-1));
  requires \valid(b + (0 .. len-1));
  requires \forall integer i; 0 <= i < len-1 ==> a[i] <= a[i+1];
  requires \forall integer i; 0 <= i < len-1 ==> b[i] <= b[i+1];
  // For even len, ensure that the sum does not overflow when computed in int.
  requires len % 2 == 0 ==> 
      (((long)a[len/2 - 1] + (long)b[0]) <= INT_MAX &&
       ((long)a[len/2 - 1] + (long)b[0]) >= INT_MIN);
  assigns \nothing;
  ensures \result == (len % 2 == 0 
                      ? (a[len/2 - 1] + b[0]) / 2 
                      : a[len/2]);
*/

