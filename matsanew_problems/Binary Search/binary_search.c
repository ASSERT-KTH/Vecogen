int binary_search(int arr[], int n, int x)
{
    /*@
      loop invariant 0 <= low <= high <= n - 1;
      loop invariant \forall integer k; 0 <= k < low ==> arr[k] < x;
      loop invariant \forall integer k; high < k <= n - 1 ==> arr[k] > x;
      loop assigns low, high;
      loop variant high - low;
     */
    int low = 0;
    int high = n - 1;

    while (low <= high)
    {
        int mid = low + (high - low) / 2;

        if (arr[mid] == x)
        {
            //@ assert contains(arr, 0, n-1, x);
            return mid;
        }
        else if (arr[mid] < x)
        {
            low = mid + 1;
        }
        else
        {
            high = mid - 1;
        }
    }

    //@ assert !contains(arr, 0, n-1, x);
    return -1;
}
