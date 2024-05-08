#include <stdio.h>

// The function declaration
void maxCells(int n, int m, int s, long long int *out);

// A structure for the test cases
typedef struct
{
    int n;
    int m;
    int s;
    long long int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {2, 3, 1000000, 6},
    {1000000, 1000000, 1, 1000000000000},
    {1000000, 1000000, 2, 1000000000000},
    {1000000, 1000000, 999999, 4},
    {1000000, 1000000, 12345, 20340100},
    {1000000, 1000000, 123456, 12358324224},
    {43496, 179847, 327622, 7822625112},
    {105126, 379125, 460772, 39855894750},
    {999463, 261665, 981183, 9566472400},
    {836832, 336228, 50, 100850467200},
    {303307, 400683, 999941, 121529958681},
    {3, 3, 2, 4},
    {40224, 890892, 54, 31858297920},
    {109785, 447109, 990618, 49085861565},
    {228385, 744978, 699604, 20725481980},
    {694117, 431924, 737, 13934440800},
    {923179, 799988, 998430, 738532121852},
    {61043, 55049, 998379, 3360356107},
    {402841, 635488, 997633, 256000621408},
    {213927, 672636, 865, 27867287808},
    {391814, 220151, 3756, 16977831150},
    {313667, 778854, 999813, 244300797618},
    {1, 2, 3, 2},
    {933241, 558702, 1, 521403613182},
    {38614, 941895, 999986, 36370333530},
    {242366, 216591, 4, 19685613696},
    {282798, 941695, 999998, 266309462610},
    {43054, 191, 1, 8223314},
    {4, 5, 6, 20},
    {9, 8, 7, 8},
    {1000, 1000, 1000, 1000000},
    {1, 1, 1, 1},
    {1, 1, 2, 1},
    {1, 1, 1000000, 1},
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
        long long int out;

        // Run the function
        maxCells(tests[i].n, tests[i].m, tests[i].s, &out);

        // Check if the result is correct
        if (out == tests[i].out)
        {
            passed++;
            printf("Test %d passed\n", i + 1);
        }
        else
        {
            printf("Expected %lld but got %lld\n", tests[i].out, out);
            printf("Test %d failed\n", i + 1);
        }

        // Print results to the file as JSON
        fprintf(file, "    {\n");
        fprintf(file, "        \"test_case\": %d,\n", i + 1);
        fprintf(file, "        \"inputs\": {\"n\": %d, \"m\": %d, \"s\": %d},\n", tests[i].n, tests[i].m, tests[i].s);
        fprintf(file, "        \"expected_output\": %lld,\n", tests[i].out);
        fprintf(file, "        \"received_output\": %lld,\n", out);
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