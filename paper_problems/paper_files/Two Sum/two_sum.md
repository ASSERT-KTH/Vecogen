# Write Up

This code was taken from the following source: https://github.com/nhtnhan/MSR2022_Copilot/blob/main/output/leetcode/leetcode_submissions7.json (Lines: 274 - 286)

## Results

- This Copilot suggestion was taken from: https://github.com/nhtnhan/MSR2022_Copilot/blob/main/output/leetcode/leetcode_submissions7.json (Lines: 274 - 286):
    - Here is the artifact from the paper by Nguyen and Nadi:

    ```
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
    "code": "class Solution(object):\n    def twoSum(self, nums, target):\n         \"\"\"\n        :type nums: List[int]\n        :type target: int\n        :rtype:    List[int]\n        \"\"\"\n        for i in range(len(nums)):\n            for j   in range(i+1, len(nums)):\n                if nums[i] + nums[j] ==    target:\n                    return [i, j]",
    "compare_result": "111111111111111111111111111111111111111111111111111111111",
    "title_slug": "two-sum"
    ```

- The LeetCode questions is asking for an algorithm that will return two unique indices of two elements which sum to a target value.
    - The program will take two inputs, one being an array of integers called `nums`, and another that is an integer called `target`.
    - The proposed algorithm should return the indices of two elements in `nums` which sum to `target`.

- The suggested algorithm from Copilot was:
    ```
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
    ```

- This solution passed all of the LeetCode test cases.
    - LeetCode Question url: https://leetcode.com/problems/two-sum/ 

- LeetCode test cases would tell us this is a correct solution.
    - This can be taken a step further and we can attempt to verify the solution using dafny.

- LeetCode provides us with the following constraints:
    - 2 <= nums/Length <= 10^4
    - -10^9 <= nums[i] <= 10^9
    - -10^9 <= target <= 10^9
    - A valid answer always exists

- Combining the constraints and the objective of the question we can produce the following FOL to define the formal specifications of our solution:
    - requires 2 <= nums.Length
    - requires exists i, j :: (0 <= i < j < nums.Length && nums[i] + nums[j] == target)
    - ensures index1 != index2
    - ensures 0 <= index1 < nums.Length
    - ensures 0 <= index2 < nums.Length
    - ensures nums[index1] + nums[index2] == target

- Now that the formal specifications are defined the python program was then translated to dafny.

- The next step was to reason about the dafny program (adding the formal specs and loop invariants).

- With some effort, we generated loop invariants that satisfied Dafny.