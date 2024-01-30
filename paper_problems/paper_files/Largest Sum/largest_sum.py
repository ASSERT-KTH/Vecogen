#-------------------------------------------------------------------------------
# Formal Specifications:
#-------------------------------------------------------------------------------
# requires 0 < len(arr) <= 10000
# ensures returns an integer = max sum of contiguous subarray

#-------------------------------------------------------------------------------
# Copilot Code: (starts)
#-------------------------------------------------------------------------------
def largest_sum(nums: list) -> int:
    """
    Kadane's algorithm
    """
    max_sum = 0
    current_sum = 0
    for num in nums:
        current_sum += num
        if current_sum > max_sum:
            max_sum = current_sum
        if current_sum < 0:
            current_sum = 0
    return max_sum
#-------------------------------------------------------------------------------
# Copilot Code: (ends)
#-------------------------------------------------------------------------------

nums = [-2, 1, -3, 4, -1, 2, 1, -5, 4]
print(largest_sum(nums))

