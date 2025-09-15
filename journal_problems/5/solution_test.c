
#include <stdio.h>

// Definition of the struct used by compare()
struct SolutionComparator
{
    int getValue;
    int solutionCost;
};

// The function declaration
int compare(struct SolutionComparator o1, struct SolutionComparator o2, int h);

// A structure for the test cases
typedef struct
{
    struct SolutionComparator o1;
    struct SolutionComparator o2;
    int h;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    // 1) both -1 => 0
    {{5, 2}, {5, 2}, 7, 0},  // same value & cost -> 0
    {{5, 1}, {5, 4}, 0, -1}, // same value, o1 cheaper -> -1
    {{3, 0}, {7, 9}, 5, 0},  // equal distance to h -> 0
    {{2, 2}, {4, 2}, 5, 1},  // o1 farther from h -> 1
    // 5) v1>=0, v2=-1 => -1
    {{0, 4}, {-1, 5}, 20, -1},
    // 6) v1>=0, v2=-1, another => -1
    {{5, 1}, {-1, 9}, 99, -1},
    // 7) v1==v2, cost equal => 0
    {{3, 5}, {3, 5}, 7, 0},
    // 8) v1==v2, cost1<cost2 => -1
    {{3, 2}, {3, 4}, 5, -1},
    // 9) v1==v2, cost1>cost2 => 1
    {{3, 7}, {3, 1}, 5, 1},
    // 10) v1!=v2, abs(h-v1)>abs(h-v2) => 1
    {{2, 0}, {5, 0}, 4, 1},
    // 11) v1!=v2, abs(h-v1)<abs(h-v2) => -1
    {{2, 0}, {5, 0}, 0, -1},
    // 12) v1!=v2, abs equal => 0
    {{2, 0}, {6, 0}, 4, 0},
    // 13) boundary: v1=0, v2=10, h=0 => -1
    {{0, 1}, {10, 1}, 0, -1},
    // 14) boundary: v1=10, v2=0, h=10 => -1
    {{10, 2}, {0, 2}, 10, -1},
    // 15) boundary: v1=0, v2=10, h=10 => 1
    {{0, 2}, {10, 2}, 10, 1},
    // 16) small values: abs1<abs2 => -1
    {{1, 0}, {2, 0}, 1, -1},
    // 17) small values: abs1>abs2 => 1
    {{1, 0}, {2, 0}, 2, 1},
    // 18) equal distance => 0
    {{5, 0}, {7, 0}, 6, 0},
    // 19) abs1<abs2 => -1
    {{9, 0}, {8, 0}, 9, -1},
    // 20) abs1>abs2 => 1
    {{9, 0}, {8, 0}, 8, 1},
    // 21) abs1>abs2 => 1
    {{4, 0}, {9, 0}, 7, 1},
    // 22) abs1>abs2 => 1
    {{4, 0}, {9, 0}, 9, 1},
    // 23) abs1<abs2 => -1
    {{4, 0}, {9, 0}, 4, -1},
    // 24) abs1<abs2 => -1
    {{6, 0}, {3, 0}, 5, -1},
    // 25) abs1>abs2 => 1
    {{6, 0}, {3, 0}, 1, 1},
    // 26) abs1>abs2 => 1
    {{6, 0}, {3, 0}, 4, 1},
    // 27) equal distance => 0
    {{0, 0}, {10, 0}, 5, 0},
    // 28) equal distance => 0
    {{10, 0}, {0, 0}, 5, 0},
    // 29) equal v, boundary, cost equal => 0
    {{10, 3}, {10, 3}, 50, 0},
    // 30) equal v, boundary, cost1<cost2 => -1
    {{10, 4}, {10, 6}, 50, -1}};

// Get the number of test cases
int num_tests = sizeof(tests) / sizeof(tests[0]);

// The main function
int main(int argc, char *argv[])
{
    if (argc < 2)
    {
        printf("Usage: %s <output_filename>\n", argv[0]);
        return 1;
    }

    const char *filename = argv[1];
    int passed = 0;
    FILE *file = fopen(filename, "w");
    if (file == NULL)
    {
        printf("Failed to open file: %s\n", filename);
        return 1;
    }

    fprintf(file, "[\n");

    for (int i = 0; i < num_tests; i++)
    {
        int out;

        // Run the function
        out = compare(tests[i].o1, tests[i].o2, tests[i].h);

        if (out == tests[i].out)
        {
            passed++;
            printf("Test %d passed\n", i + 1);
        }
        else
        {
            printf("Test %d failed (expected %d, got %d)\n",
                   i + 1, tests[i].out, out);
        }

        // Print results as JSON
        fprintf(file, "    {\n");
        fprintf(file, "        \"test_case\": %d,\n", i + 1);
        fprintf(file,
                "        \"inputs\": {\"o1\": {\"getValue\": %d, \"solutionCost\": %d}, "
                "\"o2\": {\"getValue\": %d, \"solutionCost\": %d}, \"h\": %d},\n",
                tests[i].o1.getValue, tests[i].o1.solutionCost,
                tests[i].o2.getValue, tests[i].o2.solutionCost,
                tests[i].h);
        fprintf(file, "        \"expected_output\": %d,\n", tests[i].out);
        fprintf(file, "        \"received_output\": %d,\n", out);
        fprintf(file, "        \"passed\": %s\n",
                (out == tests[i].out) ? "true" : "false");
        fprintf(file, "    },\n");
    }

    fprintf(file, "    {\n");
    fprintf(file, "        \"summary\": {\n");
    fprintf(file, "            \"total\": %d,\n", num_tests);
    fprintf(file, "            \"passed\": %d,\n", passed);
    fprintf(file, "            \"failed\": %d,\n", num_tests - passed);
    fprintf(file, "            \"pass_rate\": %.2f\n",
            (float)passed / num_tests);
    fprintf(file, "        }\n");
    fprintf(file, "    }\n");

    fprintf(file, "]\n");
    fclose(file);
    return 0;
}
