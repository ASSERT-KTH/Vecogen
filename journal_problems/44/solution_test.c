#include <stdio.h>

typedef struct {
    int a, b, c;
    int d, e, f;
    int g, h, i;
} magic_square;

// The function declaration
magic_square restoreMagicSquare(int a, int b, int c, int d, int e, int f, int g, int h, int i);

// A structure for the test cases
typedef struct
{
    int a;
    int b;
    int c;
    int d;
    int e;
    int f;
    int g;
    int h;
    int i;
    int out_a;
    int out_b;
    int out_c;
    int out_d;
    int out_e;
    int out_f;
    int out_g;
    int out_h;
    int out_i;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1},
    {0, 99626, 99582, 99766, 0, 99258, 99442, 99398, 0, 99328, 99626, 99582, 99766, 99512, 99258, 99442, 99398, 99696},
    {0, 99978, 99920, 99950, 0, 99918, 99948, 99890, 0, 99904, 99978, 99920, 99950, 99934, 99918, 99948, 99890, 99964},
    {0, 840, 666, 612, 0, 948, 894, 720, 0, 834, 840, 666, 612, 780, 948, 894, 720, 726},
    {0, 28, 10, 12, 0, 24, 26, 8, 0, 16, 28, 10, 12, 18, 24, 26, 8, 20},
    {0, 120, 83, 98, 0, 90, 105, 68, 0, 79, 120, 83, 98, 94, 90, 105, 68, 109},
    {0, 86900, 85807, 85836, 0, 86842, 86871, 85778, 0, 86310, 86900, 85807, 85836, 86339, 86842, 86871, 85778, 86368},
    {0, 74, 78, 78, 0, 74, 74, 78, 0, 76, 74, 78, 78, 76, 74, 74, 78, 76},
    {0, 505, 681, 605, 0, 657, 581, 757, 0, 707, 505, 681, 605, 631, 657, 581, 757, 555},
    {0, 662, 918, 822, 0, 854, 758, 1014, 0, 934, 662, 918, 822, 838, 854, 758, 1014, 742},
    {0, 93, 95, 93, 0, 97, 95, 97, 0, 97, 93, 95, 93, 95, 97, 95, 97, 93},
    {0, 3, 6, 5, 0, 5, 4, 7, 0, 6, 3, 6, 5, 5, 5, 4, 7, 4},
    {0, 709, 712, 719, 0, 695, 702, 705, 0, 700, 709, 712, 719, 707, 695, 702, 705, 714},
    {0, 7, 6, 9, 0, 1, 4, 3, 0, 2, 7, 6, 9, 5, 1, 4, 3, 8},
    {0, 9, 2, 3, 0, 7, 8, 1, 0, 4, 9, 2, 3, 5, 7, 8, 1, 6},
    {0, 1, 43, 13, 0, 61, 31, 73, 0, 67, 1, 43, 13, 37, 61, 31, 73, 7},
    {0, 100000, 100000, 100000, 0, 100000, 100000, 100000, 0, 100000, 100000, 100000, 100000, 100000, 100000, 100000, 100000, 100000},
    {0, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 4, 4, 4, 4, 4},
    {0, 54, 48, 36, 0, 78, 66, 60, 0, 69, 54, 48, 36, 57, 78, 66, 60, 45},
    {0, 17, 14, 15, 0, 15, 16, 13, 0, 14, 17, 14, 15, 15, 15, 16, 13, 16},
    {0, 97, 56, 69, 0, 71, 84, 43, 0, 57, 97, 56, 69, 70, 71, 84, 43, 83},
    {0, 1099, 1002, 1027, 0, 1049, 1074, 977, 0, 1013, 1099, 1002, 1027, 1038, 1049, 1074, 977, 1063},
    {0, 98721, 99776, 99575, 0, 99123, 98922, 99977, 0, 99550, 98721, 99776, 99575, 99349, 99123, 98922, 99977, 99148},
    {0, 6361, 2304, 1433, 0, 8103, 7232, 3175, 0, 5639, 6361, 2304, 1433, 4768, 8103, 7232, 3175, 3897},
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
        magic_square result;

        // Run the function
        result = restoreMagicSquare(tests[i].a, tests[i].b, tests[i].c, tests[i].d, tests[i].e, tests[i].f, tests[i].g, tests[i].h, tests[i].i);

        // Check if the result is correct
        if (result.a == tests[i].out_a &&
            result.b == tests[i].out_b &&
            result.c == tests[i].out_c &&
            result.d == tests[i].out_d &&
            result.e == tests[i].out_e &&
            result.f == tests[i].out_f &&
            result.g == tests[i].out_g &&
            result.h == tests[i].out_h &&
            result.i == tests[i].out_i)
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
        fprintf(file, "        \"input\": {\n");
        fprintf(file, "            \"a\": %d,\n", tests[i].a);
        fprintf(file, "            \"b\": %d,\n", tests[i].b);
        fprintf(file, "            \"c\": %d,\n", tests[i].c);
        fprintf(file, "            \"d\": %d,\n", tests[i].d);
        fprintf(file, "            \"e\": %d,\n", tests[i].e);
        fprintf(file, "            \"f\": %d,\n", tests[i].f);
        fprintf(file, "            \"g\": %d,\n", tests[i].g);
        fprintf(file, "            \"h\": %d,\n", tests[i].h);
        fprintf(file, "            \"i\": %d\n", tests[i].i);
        fprintf(file, "        },\n");
        fprintf(file, "        \"output\": {\n");
        fprintf(file, "            \"a\": %d,\n", result.a);
        fprintf(file, "            \"b\": %d,\n", result.b);
        fprintf(file, "            \"c\": %d,\n", result.c);
        fprintf(file, "            \"d\": %d,\n", result.d);
        fprintf(file, "            \"e\": %d,\n", result.e);
        fprintf(file, "            \"f\": %d,\n", result.f);
        fprintf(file, "            \"g\": %d,\n", result.g);
        fprintf(file, "            \"h\": %d,\n", result.h);
        fprintf(file, "            \"i\": %d\n", result.i);
        fprintf(file, "        },\n");
        fprintf(file, "        \"passed\": %s\n", (result.a == tests[i].out_a && result.b == tests[i].out_b && result.c == tests[i].out_c && result.d == tests[i].out_d && result.e == tests[i].out_e && result.f == tests[i].out_f && result.g == tests[i].out_g && result.h == tests[i].out_h && result.i == tests[i].out_i) ? "true" : "false");
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