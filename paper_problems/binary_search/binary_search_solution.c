#include <stdio.h>

// Precondition: a is a sorted array of length n
int binary_search(int arr[], int target_value, int n)
{
    int left = 0;      // Get the left most index of the array
    int right = n - 1; // Get the right most index of the array

    // While there are still numbers in the range between (l, r)
    while (left <= right)
    {
        // Calculate the new index by taking the average, and then converting to an int
        int m = (left + right) / 2;

        // Print the value of the indices
        printf("left: %d, right: %d, m: %d with value %d \n", left, right, m, arr[m]);

        if (arr[m] < target_value)
        {
            // The value is in the right half of the array
            left = m + 1;
        }
        else if (arr[m] > target_value)
        {
            right = m - 1;
        }
        else
        {
            return m;
        }
    }
    return -1;
}

int main(void)
{
    // Create the array to be sorted, numbers 1 to 100
    int arr[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
                 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
                 21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
                 31, 32, 33, 34, 35, 36, 37, 38, 39, 40,
                 41, 42, 43, 44, 45, 46, 47, 48, 49, 50,
                 51, 52, 53, 54, 55, 56, 57, 58, 59, 60,
                 61, 62, 63, 64, 65, 66, 67, 68, 69, 70,
                 71, 72, 73, 74, 75, 76, 77, 78, 79, 80,
                 81, 82, 83, 84, 85, 86, 87, 88, 89, 90,
                 91, 92, 93, 94, 95, 96, 97, 98, 99, 100};

    // Get the size of the array
    int n = sizeof(arr) / sizeof(arr[0]);

    // The target value
    int target_value = 1;

    // Get the index of the target value
    int result = binary_search(arr, target_value, n);

    // Print the result
    if (result == -1)
    {
        printf("Element is not present in array");
    }
    else
    {
        printf("Element is present at index %d", result);
    }
    return 0;
}