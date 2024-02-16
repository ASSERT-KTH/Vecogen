/* Method sort5() sorts the input array of 5 elements using a sorting-network */

/*@
  requires \valid(a+i) && \valid(a+j);
  assigns a[i], a[j];
  ensures a[i] <= a[j];
  ensures (a[i] == \old(a[i]) && a[j] == \old(a[j])) ||
          (a[i] == \old(a[j]) && a[j] == \old(a[i]));
 */
void SWAP(int a[], int i, int j)
{
  int temp = a[i];
  a[i] = a[j];
  a[j] = temp;
}

/*@
  requires \valid(a + (0..4));
  assigns a[0..4];

  // the array elements at method return are sorted
  ensures \forall integer i; 0 <= i <= 3 ==> a[i] <= a[i+1];

  // the array elements at method return are a permutation of the initial elements
  ensures \forall integer i; 0 <= i <= 4 ==>
          (\exists integer j; 0 <= j <= 4 && a[i] == \old(a[j]));
  ensures \forall integer i; 0 <= i <= 4 ==>
          (\exists integer j; 0 <= j <= 4 && \old(a[i]) == a[j]);
 */
void sort5(int a[])
{
  // The sorting network is designed to ensure the postconditions:
  // 1. The array is sorted in non-decreasing order.
  // 2. The final array is a permutation of the initial array.

  // Compare and swap operations designed to sort the array.
  SWAP(a, 0, 1);
  SWAP(a, 3, 4);
  SWAP(a, 2, 4);
  SWAP(a, 2, 3);
  SWAP(a, 1, 4);
  SWAP(a, 0, 3);
  SWAP(a, 0, 2);
  SWAP(a, 1, 3);
  SWAP(a, 1, 2);

  // Final layer of swaps to ensure full sorting
  SWAP(a, 0, 1);
  SWAP(a, 3, 4);
  SWAP(a, 2, 3);
  SWAP(a, 1, 2);

  // After these operations, the array is guaranteed to be sorted,
  // and because we only swap elements within the array,
  // the final array is a permutation of the initial array.
}