// Copilot Function converted to Dafny
method maxSubArray(nums: array<int>) returns (sum: int)
    // Requires from LeetCode description:
    requires 1 <= nums.Length <= 1000000
    requires forall i :: 0 <= i < nums.Length ==> -100000 <= nums[i] <= 100000
    // Ensures:
    ensures max_sum_subarray(nums, sum, 0, nums.Length)
{
    var max_sum := nums[0];
    var cur_sum := nums[0];
    
    var i := 1;
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant max_sum_subarray(nums, max_sum, 0, i)
        invariant forall j :: 0 <= j < i ==> Sum_Array(nums, j, i) <= cur_sum
    {
        cur_sum := max(nums[i], cur_sum + nums[i]);
        max_sum := max(max_sum, cur_sum);
        i := i + 1;
    }
    return max_sum;
}

// Function to return the max of two integers
function method max(x: int, y: int): int
{
    if x > y then x else y
}

// Predicate to confirm that sum is the maximum summation of element [start, stop) 
predicate max_sum_subarray(arr: array<int>, sum: int, start: int, stop: int)
    requires arr.Length > 0
    requires 0 <= start <= stop <= arr.Length
    reads arr
{
    forall u, v :: start <= u < v <= stop ==> Sum_Array(arr, u, v) <= sum
}

//Sums array elements between [start, stop)
function Sum_Array(arr: array<int>, start: int, stop: int): int
    requires 0 <= start <= stop <= arr.Length
    decreases stop - start
    reads arr
{
    if start >= stop then 0
    else arr[stop-1] + Sum_Array(arr, start, stop-1)
}
