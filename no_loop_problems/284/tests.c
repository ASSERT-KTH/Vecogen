#include <stdio.h>

// The function declaration
void calculateSharedTime(long l1, long r1, long l2, long r2, long k, long *out);

// A structure for the test cases
typedef struct
{
    long l1;
    long r1;
    long l2;
    long r2;
    long k;
    long out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {1, 10, 9, 20, 1, 2},
    {1, 100, 50, 200, 75, 50},
    {6, 6, 5, 8, 9, 1},
    {1, 1000000000, 1, 1000000000, 1, 999999999},
    {5, 100, 8, 8, 8, 0},
    {1, 1000000000000000000, 2, 99999999999999999, 1000000000, 99999999999999997},
    {1, 1, 1, 1, 1, 0},
    {1, 2, 3, 4, 5, 0},
    {1, 1000000000, 2, 999999999, 3141592, 999999997},
    {24648817341102, 41165114064236, 88046848035, 13602161452932, 10000831349205, 0},
    {1080184299348, 34666828555290, 6878390132365, 39891656267344, 15395310291636, 27788438422925},
    {11814, 27385, 22309, 28354, 23595, 5076},
    {4722316546398, 36672578279675, 796716437180, 33840047334985, 13411035401708, 29117730788587},
    {14300093617438, 14381698008501, 6957847034861, 32510754974307, 66056597033082, 81604391064},
    {700062402405871919, 762322967106512617, 297732773882447821, 747309903322652819, 805776739998108178, 47247500916780901},
    {59861796371397621, 194872039092923459, 668110259718450585, 841148673332698972, 928360292123223779, 0},
    {298248781360904821, 346420922793050061, 237084570581741798, 726877079564549183, 389611850470532358, 48172141432145241},
    {420745791717606818, 864206437350900994, 764928840030524015, 966634105370748487, 793326512080703489, 99277597320376979},
    {519325240668210886, 776112702001665034, 360568516809443669, 875594219634943179, 994594983925273138, 256787461333454149},
    {170331212821058551, 891149660635282032, 125964175621755330, 208256491683509799, 526532153531983174, 37925278862451249},
    {1, 3, 3, 5, 3, 0},
    {1, 5, 8, 10, 9, 0},
    {1, 2, 4, 5, 10, 0},
    {1, 2, 2, 3, 5, 1},
    {2, 4, 3, 7, 3, 1},
    {1, 2, 9, 10, 1, 0},
    {5, 15, 1, 10, 5, 5},
    {1, 4, 9, 20, 25, 0},
    {2, 4, 1, 2, 5, 1},
    {10, 1000, 1, 100, 2, 91},
    {1, 3, 3, 8, 10, 1},
    {4, 6, 6, 8, 9, 1},
    {2, 3, 1, 4, 3, 1},
    {1, 2, 2, 3, 100, 1},
    {1, 2, 100, 120, 2, 0},
    {1, 3, 5, 7, 4, 0},
    {1, 3, 5, 7, 5, 0},
    {1, 4, 8, 10, 6, 0},
    {1, 2, 5, 6, 100, 0},
    {1, 2, 5, 10, 20, 0},
    {1, 2, 5, 6, 7, 0},
    {2, 5, 7, 12, 6, 0},
    {10, 20, 50, 100, 80, 0},
    {1, 2, 5, 10, 2, 0},
    {1, 2, 5, 6, 4, 0},
    {5, 9, 1, 2, 3, 0},
    {50, 100, 1, 20, 3, 0},
    {10, 20, 3, 7, 30, 0},
    {1, 5, 10, 10, 100, 0},
    {100, 101, 1, 2, 3, 0},
    {1, 5, 10, 20, 6, 0},
    {1, 10, 15, 25, 5, 0},
    {1, 2, 5, 10, 3, 0},
    {2, 3, 5, 6, 100, 0},
    {1, 2, 4, 5, 6, 0},
    {6, 10, 1, 2, 40, 0},
    {20, 30, 1, 5, 1, 0},
    {20, 40, 50, 100, 50, 0},
    {1, 1, 4, 9, 2, 0},
    {1, 2, 5, 6, 1, 0},
    {1, 100, 400, 500, 450, 0},
    {5, 6, 1, 2, 5, 0},
    {1, 10, 21, 30, 50, 0},
    {100, 200, 300, 400, 101, 0},
    {2, 8, 12, 16, 9, 0},
    {1, 5, 7, 9, 6, 0},
    {300, 400, 100, 200, 101, 0},
    {1, 2, 2, 3, 10, 1},
    {1, 10, 100, 200, 5, 0},
    {1, 3, 3, 4, 4, 1},
    {10, 20, 30, 40, 25, 0},
    {1, 2, 5, 10, 1, 0},
    {2, 4, 8, 10, 1, 0},
    {2, 5, 10, 15, 7, 0},
    {100, 200, 5, 10, 1, 0},
    {1, 2, 100, 200, 300, 0},
    {30, 100, 10, 20, 25, 0},
    {10, 20, 1, 5, 6, 0},
    {4, 5, 1, 2, 4, 0},
    {11, 100, 1, 9, 1000, 0},
    {1, 1, 10, 10, 228, 0},
    {5, 7, 10, 20, 15, 0},
    {1, 3, 8, 9, 7, 0},
    {1, 10, 2, 8, 8, 6},
    {1, 5, 9, 15, 1, 0},
    {1, 3, 5, 6, 12, 0},
    {1, 100, 500, 1000, 3, 0},
    {1, 1, 1, 1, 2, 1},
    {1, 1000, 100, 1000, 200, 900},
    {4, 5, 1, 4, 1, 1},
    {1, 5, 5, 7, 3, 1},
    {1, 4, 4, 10, 11, 1},
    {1, 1, 3, 4, 100, 0},
    {1, 4, 3, 5, 6, 2},
    {10, 100, 20, 30, 40, 11},
    {5, 9, 1, 11, 7, 4},
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
        calculateSharedTime(tests[i].l1, tests[i].r1, tests[i].l2, tests[i].r2, tests[i].k, &out);

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
        fprintf(file, "        \"inputs\": {\"l1\": %ld, \"r1\": %ld, \"l2\": %ld, \"r2\": %ld, \"k\": %ld},\n", tests[i].l1, tests[i].r1, tests[i].l2, tests[i].r2, tests[i].k);
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