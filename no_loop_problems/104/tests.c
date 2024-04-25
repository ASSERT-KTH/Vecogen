#include <stdio.h>

// The function declaration
void calculateMaxSurvivalTime(int d, int L, int v1, int v2, int *out);

// A structure for the test cases
typedef struct
{
    int d;
    int L;
    int v1;
    int v2;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {2, 6, 2, 2, 1.000000000000000},
    {1, 10000, 10000, 10000, 0.499950000000000},
    {3274, 4728, 888, 4578, 0.266008049762166},
    {4600, 9696, 5634, 8248, 0.367094078663017},
    {2255, 7902, 8891, 429, 0.605901287553648},
    {6745, 9881, 2149, 9907, 0.260119442601194},
    {4400, 8021, 6895, 2089, 0.403049866429208},
    {5726, 9082, 7448, 3054, 0.319558179394401},
    {3381, 9769, 4898, 2532, 0.859757738896366},
    {1036, 6259, 5451, 4713, 0.513872491145218},
    {5526, 6455, 197, 4191, 0.211713764813127},
    {1, 9, 1, 2, 2.666666666666667},
    {1196, 4082, 4071, 9971, 0.205526278307933},
    {8850, 9921, 8816, 9449, 0.058636736928552},
    {3341, 7299, 2074, 8927, 0.359785474047814},
    {7831, 8609, 6820, 2596, 0.082625318606627},
    {2322, 7212, 77, 4778, 1.007209062821833},
    {9976, 9996, 4823, 4255, 0.002203128442388},
    {7631, 9769, 5377, 6437, 0.180971728457762},
    {8957, 9525, 8634, 107, 0.064981123441254},
    {6612, 9565, 3380, 2288, 0.520995059985886},
    {1103, 6256, 3934, 9062, 0.396506617420745},
    {1, 10000, 1, 1, 4999.500000000000000},
    {1854, 3280, 1481, 2140, 0.393813863573598},
    {9999, 10000, 10000, 10000, 0.000050000000000},
    {1023, 2340, 1029, 3021, 0.325185185185185},
    {2173, 2176, 10000, 9989, 0.000150082545400},
    {1, 2, 123, 1, 0.008064516129032},
    {123, 1242, 12, 312, 3.453703703703704},
    {2, 9997, 3, 12, 666.333333333333400},

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
        calculateMaxSurvivalTime(tests[i].d, tests[i].L, tests[i].v1, tests[i].v2, &out);

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
        fprintf(file, "        \"inputs\": {\"d\": %d, \"L\": %d, \"v1\": %d, \"v2\": %d},\n", tests[i].d, tests[i].L, tests[i].v1, tests[i].v2);
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