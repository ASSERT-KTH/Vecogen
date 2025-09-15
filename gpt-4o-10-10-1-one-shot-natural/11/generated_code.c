#include <stddef.h>

#include <limits.h>

/*In a scenario where two sorted arrays are provided, the task is to find the median value based on their combined lengths. The two arrays, denoted as a and b, must each have a length specified by the variable len. The elements in both arrays are guaranteed to be in non-decreasing order.

    Input
    The input consists of:
    - Two non-null integer arrays a and b, each containing len elements.
    - An integer len which must be greater than zero, indicating the number of elements in both arrays.

    Output
    The output is an integer that represents the median of the combined elements from the two arrays.
*/

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

int FindMedian(const int *a, const int *b, int len) {
    int getKth(int *a, int aStart, int *b, int bStart, int k) {
        if (aStart >= len) return b[bStart + k - 1];
        if (bStart >= len) return a[aStart + k - 1];
        if (k == 1) return a[aStart] < b[bStart] ? a[aStart] : b[bStart];

        int aMidVal = (aStart + k / 2 - 1 < len) ? a[aStart + k / 2 - 1] : INT_MAX;
        int bMidVal = (bStart + k / 2 - 1 < len) ? b[bStart + k / 2 - 1] : INT_MAX;
        
        if (aMidVal < bMidVal) {
            return getKth(a, aStart + k / 2, b, bStart, k - k / 2);
        } else {
            return getKth(a, aStart, b, bStart + k / 2, k - k / 2);
        }
    }
    
    if (len == 0) return 0; // Handle edge case

    if (len % 2 == 1) {
        return getKth((int *)a, 0, (int *)b, 0, len + 1);
    } else {
        int left = getKth((int *)a, 0, (int *)b, 0, len);
        int right = getKth((int *)a, 0, (int *)b, 0, len + 1);
        return (left + right) / 2;
    }
}
