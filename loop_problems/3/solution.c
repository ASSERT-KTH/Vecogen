/*
   Once Bob needed to find the second order statistics of a sequence of integer numbers. Lets choose each number from the sequence exactly once and sort them. The value on the second position is the second order statistics of the given sequence. In other words it is the smallest element strictly greater than the minimum. Help Bob solve this problem.

   Input
   The first input variable n contains integer ( 1 <= n <= 100 ) — amount of numbers in the sequence. The second input contains n integer in an array called arr — n elements of the sequence. These numbers don't exceed 100 in absolute value.

   Output
   If the given sequence has the second order statistics, output this order statistics, otherwise output -200. Examples

   Input
   4 1 2 2 -4

   Output
   1

   Input
   5 1 2 3 1 1

   Output
   2
*/

/*@
   requires 1 <= n <= 100;
   requires \valid(arr + (0..n-1));
   requires \valid(out);
   requires \separated(arr + (0..n-1), out);
   requires \forall integer i; 0 <= i < n ==> -100 <= arr[i] <= 100;
   assigns *out;
   behavior only_one_element:
      assumes \forall integer i; 0 <= i < n ==> arr[0] == arr[i];
      assigns *out;
      ensures *out == -200;
   behavior second_order_exists:
      assumes !\forall integer i; 0 <= i < n ==> arr[0] == arr[i];
      assigns *out;
      ensures \exists integer i; 0 <= i < n && arr[i] == *out;
      ensures \exists integer i, j; 0 <= i < n && 0 <= j < n && arr[i] < arr[j] &&
         \forall integer k; 0 <= k < n ==> arr[i] <= arr[k] &&
         \forall integer k; 0 <= k < n && arr[i] != arr[k] ==> arr[j] <= arr[k] &&
         !\exists integer k; 0 <= k < n && arr[i] < arr[k] < arr[j];
   disjoint behaviors;
   complete behaviors;
*/
void second_order_statistics(int n, int *arr, int *out)
{
   // Start with the assumption that the minimum and second minimum are the maximum possible value
   int min = 101, second_min = 102;

   //@ assert \forall integer i; 0 <= i < n ==> -100 <= arr[i] <= 100;
   //@ assert \forall integer i; 0 <= i < n ==> min > arr[i];
   //@ assert \forall integer i; 0 <= i < n ==> second_min > arr[i];

   // Find the minimum and second minimum
   /*@
      loop invariant i1: 0 <= i <= n;
      loop invariant i2: \forall integer j; 0 <= j < i ==> min <= arr[j];
      loop invariant i3: min == 101 ||  \exists integer j; 0 <= j < i && arr[j] == min;
      loop invariant i4: second_min == 101 || second_min == 102 ||  \exists integer j; 0 <= j < i && arr[j] == second_min;
      loop invariant i5: (i == 1) ==> \exists integer j; 0 <= j < i && arr[j] == min;
      loop invariant i6: (i >= 1 && \forall integer j; 0 <= j < i ==> arr[j] == arr[0]) ==> second_min == 101;
      loop invariant i7: (i >= 2 && \exists integer j, k; 0 <= j < i && 0 <= k < i && arr[j] != arr[k]) ==> min < second_min && \exists integer j; 0 <= j < i && arr[j] == second_min && !\exists integer k; 0 <= k < i && arr[k] > min && arr[k] < second_min;
      loop assigns i, min, second_min;
      loop variant n - i;
   */
   for (int i = 0; i < n; i++)
   {
      if (arr[i] < min)
      {
         second_min = min;
         min = arr[i];
      }
      else if (arr[i] < second_min && arr[i] > min)
      {
         second_min = arr[i];
      }
   }

   if (second_min > 100)
   {
      *out = -200;
   }
   else
   {
      *out = second_min;
   }
}