#include <stdio.h>

// The function declaration
void calculateMaxFruitsForCompote(int a, int b, int c, int *out);

// A structure for the test cases
typedef struct
{
    int a;
    int b;
    int c;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {2, 5, 7, 7},
    {4, 7, 13, 21},
    {2, 3, 2, 0},
    {1, 1, 1, 0},
    {1, 2, 4, 7},
    {1000, 1000, 1000, 1750},
    {1, 1, 4, 0},
    {1, 2, 3, 0},
    {1, 1000, 1000, 7},
    {1000, 1, 1000, 0},
    {1000, 2, 1000, 7},
    {1000, 500, 1000, 1750},
    {1000, 1000, 4, 7},
    {1000, 1000, 3, 0},
    {4, 8, 12, 21},
    {10, 20, 40, 70},
    {100, 200, 399, 693},
    {200, 400, 800, 1400},
    {199, 400, 800, 1393},
    {201, 400, 800, 1400},
    {200, 399, 800, 1393},
    {200, 401, 800, 1400},
    {200, 400, 799, 1393},
    {200, 400, 801, 1400},
    {139, 252, 871, 882},
    {109, 346, 811, 763},
    {237, 487, 517, 903},
    {161, 331, 725, 1127},
    {39, 471, 665, 273},
    {9, 270, 879, 63},
    {137, 422, 812, 959},
    {15, 313, 525, 105},
    {189, 407, 966, 1323},
    {18, 268, 538, 126},
    {146, 421, 978, 1022},
    {70, 311, 685, 490},
    {244, 405, 625, 1092},
    {168, 454, 832, 1176},
    {46, 344, 772, 322},
    {174, 438, 987, 1218},
    {144, 387, 693, 1008},
    {22, 481, 633, 154},
    {196, 280, 848, 980},
    {190, 454, 699, 1218},
    {231, 464, 928, 1617},
    {151, 308, 616, 1057},
    {88, 182, 364, 616},
    {12, 26, 52, 84},
    {204, 412, 824, 1428},
    {127, 256, 512, 889},
    {224, 446, 896, 1561},
    {146, 291, 584, 1015},
    {83, 164, 332, 574},
    {20, 38, 80, 133},
    {198, 393, 792, 1372},
    {120, 239, 480, 833},
    {208, 416, 831, 1449},
    {130, 260, 517, 903},
    {67, 134, 267, 462},
    {245, 490, 979, 1708},
    {182, 364, 727, 1267},
    {104, 208, 413, 721},
    {10, 2, 100, 7},
    {2, 100, 100, 14},
    {2, 3, 8, 7},
    {1, 2, 8, 7},
    {1, 2, 200, 7},
    {5, 4, 16, 14},
    {1, 10, 10, 7},
    {1, 4, 8, 7},
    {100, 4, 1000, 14},
    {2, 6, 12, 14},
    {10, 7, 4, 7},
    {2, 10, 100, 14},
    {2, 3, 4, 7},
    {1, 2, 999, 7},
    {1, 10, 20, 7},
    {100, 18, 20, 35},
    {100, 1, 100, 0},
    {3, 7, 80, 21},
    {2, 8, 24, 14},
    {1, 100, 100, 7},
    {2, 1, 8, 0},
    {10, 5, 23, 14},
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
        calculateMaxFruitsForCompote(tests[i].a, tests[i].b, tests[i].c, &out);

        // Check if the result is correct
        if (out == tests[i].out)
        {
            printf("Test %d passed\n", i);
            passed++;
        }
        else
        {
            printf("Test %d failed\n", i);
        }

        // Print results to the file as JSON
        fprintf(file, "    {\n");
        fprintf(file, "        \"test_case\": %d,\n", i + 1);
        fprintf(file, "        \"inputs\": {\"a\": %d, \"b\": %d, \"c\": %d},\n", tests[i].a, tests[i].b, tests[i].c);
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