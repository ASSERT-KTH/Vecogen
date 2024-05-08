/*@ predicate insertion_point{L}(integer ip, int key, int* a, integer len) =
  @   0 <= ip <= len &&
  @   (\forall integer i; 0 <= i < ip ==> \at(a[i], L) < key) &&
  @   (\forall integer i; ip <= i < len ==> key < \at(a[i], L));
  @*/

/*@ predicate sorted{L}(int* a, integer low, integer high) =
  @   \forall integer i; low <= i < high ==> \at(a[i], L) <= \at(a[i + 1], L);
  @*/

/*@ lemma mean_le:
  @   \forall integer i;
  @   \forall integer j;
  @   i <= j ==>
  @   i <= i + ((j - i) / 2) <= j;
  @*/

/*@ lemma sorted_array_index_elt_le{L}:
  @   \forall int* a;
  @   \forall integer len;
  @     \valid(a+ (0..len - 1)) ==>
  @     sorted{L}(a, 0, len - 1) ==>
  @     \forall integer i;
  @     \forall integer j;
  @       0 <= i <= len - 1 ==>
  @       0 <= j <= len - 1 ==>
  @       i <= j ==>
  @       a[i] <= a[j];
  @*/

/*@ lemma sorted_array_index_lt{L}:
  @   \forall int* a;
  @   \forall integer len;
  @     \valid(a+ (0..len - 1)) ==>
  @     sorted{L}(a, 0, len - 1) ==>
  @     \forall integer i;
  @     \forall integer j;
  @       0 <= i <= len - 1 ==>
  @       0 <= j <= len - 1 ==>
  @       a[i] < a[j] ==>
  @       i < j;
  @*/

/*@ requires
  @   len >= 0 && \valid(a+ (0..len - 1)) && sorted(a, 0, len - 1);
  @
  @ assigns
  @   \nothing;
  @
  @ behavior has_key:
  @   assumes
  @     \exists integer i; 0 <= i <= len - 1 && a[i] == key;
  @   ensures
  @     a[\result] == key;
  @
  @ behavior has_not_key:
  @   assumes
  @     \forall integer i; 0 <= i <= len - 1 ==> a[i] != key;
  @   ensures
  @     insertion_point(-\result - 1, key, a, len);
  @
  @ disjoint behaviors;
  @
  @ complete behaviors;
  @
  @*/
int binary_search(int *a, int len, int key)
{
  int low = 0;
  int high = len - 1;
  /*@ loop invariant
    @   0 <= low && high <= len - 1;
    @
    @ for has_key:
    @   loop invariant
    @     \exists integer i; low <= i <= high && a[i] == key;
    @
    @ for has_not_key:
    @   loop invariant
    @     low <= len &&
    @     (\forall integer i; 0 <= i < low ==> a[i] < key) &&
    @     (\forall integer i; high < i <= len - 1 ==> key < a[i]);
    @
    @ loop variant
    @   high - low;
    @*/
  while (low <= high)
  {
    int mid = low + ((high - low) / 2);
    int mid_val = a[mid];
    if (mid_val < key)
    {
      low = mid + 1;
    }
    else if (mid_val > key)
    {
      high = mid - 1;
    }
    else
    {
      return mid;
    }
  }
  return -low - 1;
}