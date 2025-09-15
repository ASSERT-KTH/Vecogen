#include <stdio.h>

// The function declaration
int minimumHorseshoesNeeded(int a, int b, int c, int d);

// A structure for the test cases
typedef struct
{
    int a;
    int b;
    int c;
    int d;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {1, 7, 3, 3, 1},
    {551651653, 551651653, 551651653, 551651653, 3},
    {156630260, 609654355, 668943582, 973622757, 0},
    {17061017, 110313588, 434481173, 796661222, 0},
    {24975422, 256716298, 337790533, 690960249, 0},
    {255635360, 732742923, 798648949, 883146723, 0},
    {133315691, 265159773, 734556507, 265159773, 1},
    {28442865, 741657755, 978106882, 978106882, 1},
    {131245479, 174845575, 497483467, 131245479, 1},
    {139159884, 616215581, 958341883, 616215581, 1},
    {147784432, 947653080, 947653080, 947653080, 2},
    {7, 7, 7, 7, 3},
    {94055790, 756126496, 756126496, 94055790, 2},
    {240458500, 511952208, 240458500, 511952208, 2},
    {681828506, 972810624, 972810624, 681828506, 2},
    {454961014, 454961014, 454961014, 454961014, 3},
    {915819430, 915819430, 915819430, 915819430, 3},
    {671645142, 671645142, 671645142, 671645142, 3},
    {132503558, 132503558, 132503558, 132503558, 3},
    {5, 5, 999999, 6, 1},
    {1, 1, 2, 5, 1},
    {2, 1, 2, 3, 1},
    {81170865, 673572653, 756938629, 995577259, 0},
    {1, 1, 3, 5, 1},
    {1, 1, 3, 3, 2},
    {2, 2, 2, 1, 2},
    {3, 1, 1, 1, 2},
    {1, 2, 2, 2, 2},
    {3491663, 217797045, 522540872, 715355328, 0},
    {251590420, 586975278, 916631563, 586975278, 1},
    {259504825, 377489979, 588153796, 377489979, 1},
    {652588203, 931100304, 931100304, 652588203, 2},
    {391958720, 651507265, 391958720, 651507265, 2},
    {90793237, 90793237, 90793237, 90793237, 3},
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
        out = minimumHorseshoesNeeded(tests[i].a, tests[i].b, tests[i].c, tests[i].d);

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
        fprintf(file, "        \"inputs\": {\"a\": %d, \"b\": %d, \"c\": %d, \"d\": %d},\n", tests[i].a, tests[i].b, tests[i].c, tests[i].d);
        fprintf(file, "        \"expected_output\": %d,\n", tests[i].out);
        fprintf(file, "        \"received_output\": %d,\n", out);
        fprintf(file, "        \"passed\": %s\n", out == tests[i].out ? "true" : "false");
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