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
    // Compute the effective rotation by taking modulo
    int effective_rotation = n % len;
    // Calculate the new index using the formula, safely handle integer operations
    int rotated_index = index - effective_rotation;
    if (rotated_index < 0) {
        rotated_index += len;
    }
    return l[rotated_index];
}
