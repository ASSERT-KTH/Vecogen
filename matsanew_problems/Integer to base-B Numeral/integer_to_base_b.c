/*@
  requires n >= 0 && b >= 2 && size >= 1;
  requires \valid(a + (0..size-1));
  assigns a[0..size-1];
  ensures \result == -1 ||
          (\result >= 0 && int_val1(a, \result, size-1, b) == n &&
           \forall int i; \result <= i <= size-1 ==> 0 <= a[i] < b);
 */
int int_to_seq(int n, int b, int a[], int size) {
    int index = 0;
    int remainder;

    /*@
      loop assigns index, n;
      loop invariant n >= 0;
      loop invariant index <= size;
      loop invariant \forall int i; 0 <= i < index ==> 0 <= a[i] < b;
      loop invariant int_val1(a, index, size - 1, b) == n;
      loop variant n;
     */
    while (n > 0 && index < size) {
        remainder = n % b;
        a[index++] = remainder;
        n /= b;
    }

    /*@
      loop invariant \result == -1 || (\result >= 0 && int_val1(a, \result, size-1, b) == n);
      loop invariant \forall int i; \result <= i < size ==> 0 <= a[i] < b;
     */
    if (n == 0) {
        return index;
    } else {
        return -1;
    }
}
