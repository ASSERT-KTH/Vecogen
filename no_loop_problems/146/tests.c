#include <stdio.h>

// The function declaration
void calculateMaximumMessiness(long n, int k, long *out);

// A structure for the test cases
typedef struct
{
    long n;
    int k;
    long out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {5, 2, 10},
    {1, 10, 0},
    {100000, 2, 399990},
    {1, 1, 0},
    {8, 3, 27},
    {7, 1, 11},
    {100000, 40000, 4799960000},
    {1, 1000, 0},
    {100, 45, 4905},
    {9, 2, 26},
    {456, 78, 58890},
    {100000, 50000, 4999950000},
    {100000, 50001, 4999950000},
    {100000, 50002, 4999950000},
    {100000, 50003, 4999950000},
    {100000, 49998, 4999949994},
    {100000, 49997, 4999949985},
    {99999, 49998, 4999849998},
    {99999, 49997, 4999849991},
    {99999, 49996, 4999849980},
    {99999, 50000, 4999850001},
    {99999, 50001, 4999850001},
    {99999, 50002, 4999850001},
    {30062, 9, 540945},
    {13486, 3, 80895},
    {29614, 7, 414491},
    {13038, 8, 208472},
    {96462, 6, 1157466},
    {22599, 93799, 255346101},
    {421, 36817, 88410},
    {72859, 65869, 2654180511},
    {37916, 5241, 342494109},
    {47066, 12852, 879423804},
    {84032, 21951, 2725458111},
    {70454, 75240, 2481847831},
    {86946, 63967, 3779759985},
    {71128, 11076, 1330260828},
    {46111, 64940, 1063089105},
    {46111, 64940, 1063089105},
    {56500, 84184, 1596096750},
    {60108, 83701, 1806455778},
    {1, 2, 0},
    {1, 3, 0},
    {1, 4, 0},
    {1, 5, 0},
    {1, 6, 0},
    {2, 1, 1},
    {2, 2, 1},
    {2, 3, 1},
    {2, 4, 1},
    {2, 5, 1},
    {3, 1, 3},
    {3, 2, 3},
    {3, 3, 3},
    {3, 4, 3},
    {3, 5, 3},
    {4, 1, 5},
    {4, 2, 6},
    {4, 3, 6},
    {4, 4, 6},
    {4, 5, 6},
    {5, 1, 7},
    {5, 3, 10},
    {5, 4, 10},
    {5, 5, 10},
    {6, 1, 9},
    {6, 2, 14},
    {6, 3, 15},
    {7, 2, 18},
    {7, 3, 21},
    {7, 4, 21},
    {10, 2, 30},
    {60982, 2, 243918},
    {23426, 23, 1076515},
    {444, 3, 2643},
    {18187, 433, 15374531},
    {6895, 3544, 23767065},
    {56204, 22352, 1513297456},
    {41977, 5207, 382917573},
    {78147, 2321, 351981971},
    {99742, 62198, 4974183411},
    {72099, 38339, 2599096851},
    {82532, 4838, 751762306},
    {79410, 33144, 3066847464},
    {11021, 3389, 51726307},
    {66900, 7572, 898455660},
    {99999, 49999, 4999850001},
    {100000, 49999, 4999949999},
    {100000, 100000, 4999950000},
    {100000, 1, 199997},
    {4, 100, 6},
    {100000, 1234, 243753254},
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
        long out;

        // Run the function
        calculateMaximumMessiness(tests[i].n, tests[i].k, &out);

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
        fprintf(file, "        \"inputs\": {\"n\": %ld, \"k\": %d},\n", tests[i].n, tests[i].k);
        fprintf(file, "        \"expected_output\": %ld,\n", tests[i].out);
        fprintf(file, "        \"received_output\": %ld,\n", out);
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