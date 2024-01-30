#################################################################
# All of this code / information is from: https://github.com/nhtnhan/MSR2022_Copilot/blob/main/output/leetcode/leetcode_submissions7.json (Lines: 274 - 286)
#################################################################

# Artifact Details:
'''
"id": 581843511,
"lang": "python",
"time": "3 weeks, 6 days",
"timestamp": 1636001702,
"status_display": "Accepted",
"runtime": "3524 ms",
"url": "/submissions/detail/581843511/",
"is_pending": "Not Pending",
"title": "Two Sum",
"memory": "14.2 MB",
"code": "class Solution(object):\n    def twoSum(self, nums, target):\n        \"\"\"\n        :type nums: List[int]\n        :type target: int\n        :rtype: List[int]\n        \"\"\"\n        for i in range(len(nums)):\n            for j in range(i+1, len(nums)):\n                if nums[i] + nums[j] == target:\n                    return [i, j]",
"compare_result": "111111111111111111111111111111111111111111111111111111111",
"title_slug": "two-sum"
'''


# Given an array of integers nums and an integer target, return indices
# of the two numbers such that they add up to target.

# You may assume that each input would have exactly one solution, and
# you may not use the same element twice.

# You can return the answer in any order.

class Solution(object):
    def twoSum(self, nums, target):
        """
        :type nums: List[int]
        :type target: int
        :rtype: List[int]
        """
        for i in range(len(nums)):
            for j in range(i+1, len(nums)):
                if nums[i] + nums[j] == target:
                    return [i, j]

if __name__ == "__main__":

    # Example test case
    nums = [2,7,11,15]
    target = 22
    result = Solution.twoSum(object, nums, target)
    assert result == [1, 3]
    print(f"Passed Test Case!\nOutput: {result}")