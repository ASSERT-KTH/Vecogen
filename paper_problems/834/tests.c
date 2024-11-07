#include <stdio.h>

// The function declaration
void calculateMinimumClonesForDemonstrationPercentage(int n, int x, int y, int *out);

// A structure for the test cases
typedef struct
{
    int n;
    int x;
    int y;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {10, 1, 14, 1},
    {20, 10, 50, 0},
    {1000, 352, 146, 1108},
    {68, 65, 20, 0},
    {78, 28, 27, 0},
    {78, 73, 58, 0},
    {70, 38, 66, 9},
    {54, 4, 38, 17},
    {3, 1, 69, 2},
    {11, 9, 60, 0},
    {71, 49, 65, 0},
    {78, 55, 96, 20},
    {2765, 768, 9020, 248635},
    {3478, 1728, 9727, 336578},
    {9678, 6173, 5658, 541409},
    {1138, 570, 6666, 75290},
    {7754, 204, 9038, 700603},
    {8403, 7401, 4769, 393339},
    {4909, 2111, 8860, 432827},
    {6571, 6449, 8965, 582642},
    {9178, 2255, 7996, 731618},
    {6151, 6148, 3746, 224269},
    {8890, 5449, 8734, 771004},
    {7879, 2590, 2818, 219441},
    {8484, 6400, 547, 40008},
    {7835, 6710, 1639, 121706},
    {2379, 1436, 9663, 228447},
    {6487, 5670, 8, 0},
    {4470, 2543, 6, 0},
    {7261, 5328, 10, 0},
    {3871, 3795, 7, 0},
    {9620, 6557, 6, 0},
    {4890, 1112, 5, 0},
    {1, 1, 1, 0},
    {1, 1, 10000, 99},
    {10000, 1, 1, 99},
    {10000, 1, 10000, 999999},
    {10000, 10000, 1, 0},
    {10000, 10000, 10000, 990000},
    {67, 1, 3, 2},
    {7878, 4534, 9159, 717013},
    {1, 1, 1, 0},
    {3271, 5, 50, 1631},
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
        calculateMinimumClonesForDemonstrationPercentage(tests[i].n, tests[i].x, tests[i].y, &out);

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
        fprintf(file, "        \"inputs\": {\"n\": %d, \"x\": %d, \"y\": %d},\n", tests[i].n, tests[i].x, tests[i].y);
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