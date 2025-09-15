#include <stdio.h>

// The function declaration
int calculateMinimumTimeToHouse(int n, int a);

// A structure for the test cases
typedef struct
{
    int n;
    int a;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {4, 2, 2},
    {8, 5, 3},
    {2, 1, 1},
    {2, 2, 1},
    {10, 1, 1},
    {10, 10, 1},
    {100000, 100000, 1},
    {100000, 2, 50000},
    {100000, 3, 2},
    {100000, 99999, 50000},
    {100, 100, 1},
    {3000, 34, 1484},
    {2000, 1, 1},
    {100000, 1, 1},
    {24842, 1038, 11903},
    {1628, 274, 678},
    {16186, 337, 169},
    {24562, 2009, 1005},
    {9456, 3443, 1722},
    {5610, 332, 2640},
    {1764, 1288, 239},
    {28588, 13902, 7344},
    {92480, 43074, 24704},
    {40022, 26492, 6766},
    {85766, 64050, 10859},
    {67808, 61809, 30905},
    {80124, 68695, 34348},
    {95522, 91716, 1904},
    {7752, 2915, 1458},
    {5094, 5058, 19},
    {6144, 4792, 677},
    {34334, 20793, 10397},
    {23538, 10243, 5122},
    {9328, 7933, 3967},
    {11110, 9885, 4943},
    {26096, 2778, 11660},
    {75062, 5323, 2662},
    {94790, 7722, 43535},
    {90616, 32240, 29189},
    {96998, 8992, 44004},
    {95130, 19219, 9610},
    {92586, 8812, 41888},
    {3266, 3044, 112},
    {5026, 4697, 2349},
    {3044, 2904, 71},
    {6022, 5396, 314},
    {31270, 25522, 2875},
    {82156, 75519, 37760},
    {34614, 27913, 13957},
    {88024, 61143, 30572},
    {91870, 55672, 18100},
    {95718, 4868, 45426},
    {99564, 358, 49604},
    {89266, 13047, 6524},
    {90904, 16455, 8228},
    {94750, 13761, 6881},
    {100000, 23458, 38272},
    {100000, 23457, 11729},
    {59140, 24272, 17435},
    {9860, 8516, 673},
    {25988, 2733, 1367},
    {9412, 5309, 2655},
    {25540, 23601, 11801},
    {76260, 6050, 35106},
    {92388, 39118, 26636},
    {8516, 5495, 2748},
    {91940, 37847, 18924},
    {30518, 286, 15117},
    {46646, 19345, 9673},
};

// Get the number of test cases
int num_tests = sizeof(tests) / sizeof(tests[0]);

// The main function
int main(int argc, char *argv[])
{
    if (argc < 2)
    {
        printf("Usage: %s <output_filename>\n", argv[0]);
        return 1; // Exit with error code if no filename is provided
    }

    // File name is taken from command line
    const char *filename = argv[1];

    // Keep track of the amount of passed tests
    int passed = 0;
    FILE *file = fopen(filename, "w"); // Open the file specified by command line for writing

    if (file == NULL)
    {
        printf("Failed to open file: %s\n", filename);
        return 1; // Exit with error code if file cannot be opened
    }

    // Start JSON array
    fprintf(file, "[\n");

    // For each test case try the function
    for (int i = 0; i < num_tests; i++)
    {
        // Create variables to store the output
        int out;

        // Run the function
        out = calculateMinimumTimeToHouse(tests[i].n, tests[i].a);

        // Check if the result is correct
        if (out == tests[i].out)
        {
            passed++;
            printf("Test %d passed\n", i + 1);
        }
        else
        {
            printf("Test %d failed\n", i + 1);
        }

        // Print results to the file as JSON
        fprintf(file, "    {\n");
        fprintf(file, "        \"test_case\": %d,\n", i + 1);
        fprintf(file, "        \"inputs\": {\"n\": %d, \"a\": %d},\n", tests[i].n, tests[i].a);
        fprintf(file, "        \"expected_output\": %d,\n", tests[i].out);
        fprintf(file, "        \"received_output\": %d,\n", out);
        fprintf(file, "        \"passed\": %s\n", (out == tests[i].out) ? "true" : "false");
        fprintf(file, "    },\n");
    }

    // Add summary to the file
    fprintf(file, "    {\n");
    fprintf(file, "        \"summary\": {\n");
    fprintf(file, "            \"total\": %d,\n", num_tests);
    fprintf(file, "            \"passed\": %d,\n", passed);
    fprintf(file, "            \"failed\": %d,\n", num_tests - passed);
    fprintf(file, "            \"pass_rate\": %.2f\n", (float)passed / num_tests);
    fprintf(file, "        }\n");
    fprintf(file, "    }\n");

    // End JSON array
    fprintf(file, "]\n");
    fclose(file);
    return 0;
}