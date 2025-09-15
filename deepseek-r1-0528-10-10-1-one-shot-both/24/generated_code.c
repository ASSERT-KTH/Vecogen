#include <stddef.h>

#include <limits.h>

/*In this task, you are working with an array of integers and need to compute a specific sum based on given indices. 
  The goal is to calculate the sum of elements in the array between two specified indices, inclusive of the start index and exclusive of the end index.

  Input:
  - An integer pointer a representing an array of integers.
  - An integer len, which indicates the total number of elements in the array. 
  - Two integers, start and end, which represent the range of indices. 
    The values of start and end must be such that 0 <= start <= end <= len.

  Output:
  - An integer representing the sum of the elements in the array from the index start up to, but not including, the index end. The output will always be a non-negative integer and will not exceed the maximum value for an integer.
*/

/*@ predicate InRange(int *a, integer len, integer lo, integer hi) =
      0 <= lo <= hi <= len &&
      (len == 0 || \valid(a + (0 .. len-1)));
*/

/*@ logic integer sum_interval(int *a, integer lo, integer hi) =
      (hi <= lo) ? 0 : sum_interval(a, lo, hi - 1) + a[hi - 1];
*/

/*@
  requires 0 <= len;
  requires 0 <= start <= end <= len;
  requires InRange(a, len, start, end);
  requires \forall integer x; 0 <= x < len ==> 0 <= a[x] <= 100;
  requires sum_interval(a, (int) 0, (int) (len)) <= INT_MAX;
  requires end - start <= INT_MAX / 100;
  decreases end - start;
  assigns \nothing;
  ensures \result == sum_interval(a, start, end);
  ensures (start == end) ==> (\result == 0);
  ensures start < end  
    ==> \result == sum_interval(a, start, (int)(end - 1)) + a[(int)(end - 1)];
  ensures 0 <= \result <= 100 * (end - start);
*/

int sumTo(int *a, int start, int end, int len) {
    if (start == end) {
        return 0;
    }
    else {
        return a[end-1] + sumTo(a, start, end-1, len);
    }
}
