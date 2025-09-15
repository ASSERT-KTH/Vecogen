#include <stddef.h>

/*In a scenario where you have a list of integers and you want to analyze its elements after performing a series of rotations, this function helps you determine the value at a specific position after these rotations. The goal is to find out what integer would be at a given index if the list were rotated to the right by a specified number of times.

  Input:
  - l: A pointer to an array of integers, representing the list.
  - len: An integer that indicates the length of the list, which must be greater than 0.
  - n: A non-negative integer representing the number of times the list is rotated to the right.
  - index: A non-negative integer that specifies the index in the list for which you want to find the value after the rotations. This index must be less than the length of the list.

  Output:
  - The function returns the integer value located at the specified index after the list has been effectively rotated.
*/

/*@
requires len > 0;
  requires n >= 0;
  requires index >= 0 && index < len;
  requires \valid(l + (0 .. len-1));
  assigns \nothing;
  ensures \result == l[(index - (n % len) + len) % len];
@
*/

int ElementAtIndexAfterRotation(const int *l, int len, int n, int index) {
    int k = n % len;
    int new_index = index - k;
    if (new_index < 0) {
        new_index += len;
    }
    return l[new_index];
}
