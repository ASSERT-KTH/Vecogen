# from leetcode: https://leetcode.com/problems/maximum-subarray/

# Given an integer array nums, find the contiguous subarray
# (containing at least one number) which has the largest sum and 
# return its sum.

# Copilot Solution:
class Solution(object):
    def maxSubArray(self, nums):
        """
        :type nums: List[int]
        :rtype: int
        """
        max_sum = nums[0]
        cur_sum = nums[0]
        for i in range(1, len(nums)):
            cur_sum = max(nums[i], cur_sum + nums[i])
            max_sum = max(max_sum, cur_sum)
        return max_sum

if __name__ == "__main__":

    # Example test case from LeetCode:
    nums = [-2,1,-3,4,-1,2,1,-5,4]
    answer_expected = 6
    answer_actual = Solution.maxSubArray(object, nums)
    assert answer_actual == answer_expected, f"Expected {answer_expected}, got {answer_actual}"
    print(f"Test Case Passed: {answer_actual}")