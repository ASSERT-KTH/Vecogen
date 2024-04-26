#include <stdio.h>

// The function declaration
void findPythagoreanTripleForSide(int N, long *out1, long *out2);

// A structure for the test cases
typedef struct
{
    int N;
    long out1;
    long out2;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {3, 4, 5},
    {246, 15128, 15130},
    {902, 203400, 203402},
    {1000000000, 249999999999999999, 250000000000000001},
    {1998, 998000, 998002},
    {2222222, 1234567654320, 1234567654322},
    {2222226, 1234572098768, 1234572098770},
    {1111110, 308641358024, 308641358026},
    {9999998, 24999990000000, 24999990000002},
    {1024, 262143, 262145},
    {8388608, 17592186044415, 17592186044417},
    {6, 8, 10},
    {4, 3, 5},
    {8, 15, 17},
    {16, 63, 65},
    {492, 60515, 60517},
    {493824, 60965535743, 60965535745},
    {493804, 60960597603, 60960597605},
    {493800, 60959609999, 60959610001},
    {2048, 1048575, 1048577},
    {8388612, 17592202821635, 17592202821637},
    {44, 483, 485},
    {1, -1},
    {444, 49283, 49285},
    {4444, 4937283, 4937285},
    {44444, 493817283, 493817285},
    {444444, 49382617283, 49382617285},
    {4444444, 4938270617283, 4938270617285},
    {100000000, 2499999999999999, 2500000000000001},
    {2, -1},
    {3, 4, 5},
    {5, 12, 13},
    {7, 24, 25},
    {17, 144, 145},
    {9, 40, 41},
    {11, 60, 61},
    {13, 84, 85},
    {15, 112, 113},
    {19, 180, 181},
    {111, 6160, 6161},
    {113, 6384, 6385},
    {115, 6612, 6613},
    {117, 6844, 6845},
    {119, 7080, 7081},
    {67, 2244, 2245},
    {111111, 6172827160, 6172827161},
    {111113, 6173049384, 6173049385},
    {111115, 6173271612, 6173271613},
    {111117, 6173493844, 6173493845},
    {111119, 6173716080, 6173716081},
    {9999993, 49999930000024, 49999930000025},
    {9999979, 49999790000220, 49999790000221},
    {9999990, 24999950000024, 24999950000026},
    {9999991, 49999910000040, 49999910000041},
    {9999992, 24999960000015, 24999960000017},
    {10, 24, 26},
    {9999973, 49999730000364, 49999730000365},
    {9999994, 24999970000008, 24999970000010},
    {9999995, 49999950000012, 49999950000013},
    {9999996, 24999980000003, 24999980000005},
    {9999997, 49999970000004, 49999970000005},
    {9999978, 24999890000120, 24999890000122},
    {99999993, 4999999300000024, 4999999300000025},
    {99999979, 4999997900000220, 4999997900000221},
    {99999990, 2499999500000024, 2499999500000026},
    {99999991, 4999999100000040, 4999999100000041},
    {14, 48, 50},
    {99999992, 2499999600000015, 2499999600000017},
    {99999973, 4999997300000364, 4999997300000365},
    {99999994, 2499999700000008, 2499999700000010},
    {99999995, 4999999500000012, 4999999500000013},
    {99999996, 2499999800000003, 2499999800000005},
    {99999997, 4999999700000004, 4999999700000005},
    {99999978, 2499998900000120, 2499998900000122},
    {987654323, 487730530870294164, 487730530870294165},
    {2, -1},
    {4, 3, 5},
    {22, 120, 122},
    {8, 15, 17},
    {64, 1023, 1025},
    {999999999, 499999999000000000, 499999999000000001},
    {16, 63, 65},
    {999999937, 499999937000001984, 499999937000001985},
    {999999998, 249999999000000000, 249999999000000002},
    {433494437, 93958713454973484, 93958713454973485},
    {484916147, 117571834810662804, 117571834810662805},
    {999999929, 499999929000002520, 499999929000002521},
    {982451653, 482605625241216204, 482605625241216205},
    {23, 264, 265},
    {2048, 1048575, 1048577},
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
        long out1, out2;

        // Run the function
        findPythagoreanTripleForSide(tests[i].N, &out1, &out2);

        // Check if the result is correct
        if (out1 == tests[i].out1 && out2 == tests[i].out2)
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
        fprintf(file, "        \"inputs\": {\"N\": %d},\n", tests[i].N);
        fprintf(file, "        \"expected_output\": [%ld, %ld],\n", tests[i].out1, tests[i].out2);
        fprintf(file, "        \"received_output\": [%ld, %ld],\n", out1, out2);
        fprintf(file, "        \"passed\": %s\n", (out1 == tests[i].out1 && out2 == tests[i].out2) ? "true" : "false");
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