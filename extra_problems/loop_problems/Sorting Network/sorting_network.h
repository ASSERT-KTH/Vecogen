/* Method sort5() sorts the input array of 5 elements using a sorting-network */

/*@
  requires \valid(a+i) && \valid(a+j);
  assigns a[i], a[j];
  ensures a[i] <= a[j];
  ensures (a[i] == \old(a[i]) && a[j] == \old(a[j])) ||
          (a[i] == \old(a[j]) && a[j] == \old(a[i]));
 */
void SWAP(int a[], int i, int j);

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
void sort5(int a[]);