#include <stdio.h>

// The function declaration
void star(int a, int *out);

// A structure for the test cases
typedef struct
{
    int a;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {2, 13},
    {1, 1},
    {3, 37},
    {4, 73},
    {5, 121},
    {6, 181},
    {7, 253},
    {8, 337},
    {9, 433},
    {15000, 1349910001},
    {4845, 140815081},
    {6914, 286778893},
    {3994, 95688253},
    {12504, 938025073},
    {13170, 1040614381},
    {427, 1091413},
    {11877, 846307513},
    {3202, 61497613},
    {5689, 194154193},
    {15302, 1404815413},
    {17042, 1742476333},
    {1481, 13151281},
    {15592, 1458569233},
    {16344, 1602659953},
    {4222, 106926373},
    {11808, 836502337},
    {13366, 1071819541},
    {3823, 87669037},
    {581, 2021881},
    {15479, 1437503773},
    {6543, 256825837},
    {11136, 743996161},
    {16331, 1600111381},
    {8543, 437845837},
    {7530, 340160221},
    {3154, 59667373},
    {11501, 793569001},
    {12038, 869408437},
    {13082, 1026753853},
    {18257, 1999798753},
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
        star(tests[i].a, &out);

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
        fprintf(file, "        \"inputs\": {\"a\": %d},\n", tests[i].a);
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