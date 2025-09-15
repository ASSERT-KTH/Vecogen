#include <stddef.h>

/*In a programming context, you are tasked with retrieving a specific element from an array based on its position. 
	The goal is to identify the k-th element in the array.

	Input
	- An array of integers, referred to as arr, which contains a sequence of elements.
	- An integer len, representing the total number of elements in the array, where len must be at least 1.
	- An integer k, which indicates the position of the desired element in the array, with the constraint that k must be at least 1 and at most equal to len.

	Output
	- The output is the integer value located at the k-th position in the array, where the first position is indexed as 1.
*/

/*@
requires \valid_read(arr + (0 .. len - 1));
  requires 1 <= k <= len;
  assigns \nothing;
  ensures \result == arr[k - 1];
@
*/

int kth_element(int arr[], int len, int k) {
    return arr[k-1];
}
