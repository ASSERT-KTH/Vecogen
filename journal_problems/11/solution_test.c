
#include <stdio.h>
#include <limits.h>

// Declaration of the function under test
int FindMedian(const int *a, const int *b, int len);

// A structure for the test cases
typedef struct {
    int a[10];
    int b[10];
    int len;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    // 1) len=1, odd
    {{  5, 0,0,0,0,0,0,0,0,0 }, { 10,0,0,0,0,0,0,0,0,0 },  1,  5},
    // 2) len=2, even
    {{  1, 2,0,0,0,0,0,0,0,0 }, {  3, 4,0,0,0,0,0,0,0,0 },  2,  2},
    // 3) len=2, all zero
    {{  0, 0,0,0,0,0,0,0,0,0 }, {  0, 0,0,0,0,0,0,0,0,0 },  2,  0},
    // 4) len=3, odd
    {{  1, 2, 3,0,0,0,0,0,0,0 }, {  4, 5, 6,0,0,0,0,0,0,0 },  3,  2},
    // 5) len=4, even with negatives
    {{ -5,-1, 0, 1,0,0,0,0,0,0 }, {  2, 3, 4, 5,0,0,0,0,0,0 },  4,  0},
    // 6) len=5, odd
    {{ -2,-1, 0, 1, 2,0,0,0,0,0 }, { 10,20,30,40,50,0,0,0,0,0 },  5,  0},
    // 7) len=6, even all ones/twos
    {{  1, 1, 1, 1, 1, 1,0,0,0,0 }, {  2, 2, 2, 2, 2, 2,0,0,0,0 },  6,  1},
    // 8) len=6, even large mix
    {{ 1000000000,1000000001,1000000002,1000000003,1000000004,1000000005,0,0,0,0 },
     { -1000000000,0,1,2,3,4,0,0,0,0 }, 6, 1},
    // 9) len=7, odd all ones
    {{  1, 1, 1, 1, 1, 1, 1,0,0,0 }, {  0, 0, 0, 0, 0, 0, 0,0,0,0 },  7,  1},
    //10) len=2, even negatives
    {{ -4,-3,0,0,0,0,0,0,0,0 }, { -2,-1,0,0,0,0,0,0,0,0 },  2, -3},
    //11) len=3, odd negatives
    {{ -3,-2,-1,0,0,0,0,0,0,0 }, {  0, 0, 0,0,0,0,0,0,0,0 },  3, -2},
    //12) len=4, even duplicates
    {{  2, 2, 2, 2,0,0,0,0,0,0 }, {  2, 2, 2, 2,0,0,0,0,0,0 },  4,  2},
    //13) len=5, odd mixed
    {{ -5, 0, 5,10,15,0,0,0,0,0 }, {  1, 2, 3, 4, 5,0,0,0,0,0 },  5,  5},
    //14) len=4, even interleaved
    {{  1, 3, 5, 7,0,0,0,0,0,0 }, {  2, 4, 6, 8,0,0,0,0,0,0 },  4,  2},
    //15) len=3, odd zeros
    {{  0, 0, 1,0,0,0,0,0,0,0 }, {  5, 6, 7,0,0,0,0,0,0,0 },  3,  0},
    //16) len=2, even mix negatives
    {{ -1, 0,0,0,0,0,0,0,0,0 }, { -2,-1,0,0,0,0,0,0,0,0 },  2, -1},
    //17) len=5, odd all equal
    {{  4, 4, 4, 4, 4,0,0,0,0,0 }, {  1, 2, 3, 4, 5,0,0,0,0,0 },  5,  4},
    //18) len=6, even zeros/twos
    {{  0, 0, 0, 0, 0, 0,0,0,0,0 }, {  1, 1, 1, 1, 1, 1,0,0,0,0 },  6,  0},
    //19) len=5, odd negative mix
    {{ -10,-5, 0, 5,10,0,0,0,0,0 }, {  0, 0, 0, 0, 0,0,0,0,0,0 },  5,  0},
    //20) len=4, even single negative
    {{ -3, 0, 3, 6,0,0,0,0,0,0 }, { -2, 1, 4, 7,0,0,0,0,0,0 },  4, -1},
    //21) len=3, odd all same negative
    {{ -5,-5,-5,0,0,0,0,0,0,0 }, { -1,-1,-1,0,0,0,0,0,0,0 },  3, -5},
    //22) len=2, even half-int max
    {{  INT_MAX/2, INT_MAX/2 + 1,0,0,0,0,0,0,0,0 },
     { -INT_MAX/2,    -INT_MAX/2 + 2,0,0,0,0,0,0,0,0 },   2,  0},
    //23) len=2, even cross zero
    {{ -100,100,0,0,0,0,0,0,0,0 }, { -50, 50,0,0,0,0,0,0,0,0 },  2,-75},
    //24) len=1, odd zero
    {{   0, 0,0,0,0,0,0,0,0,0 }, {12345,0,0,0,0,0,0,0,0,0 },  1,  0},
    //25) len=7, odd consecutive
    {{ 1,2,3,4,5,6,7,0,0,0 }, {8,9,10,11,12,13,14,0,0,0}, 7, 4},
    //26) len=8, even consecutive
    {{ 1,2,3,4,5,6,7,8,0,0 }, {9,10,11,12,13,14,15,16,0,0}, 8, 6},
    //27) len=8, even negatives mix
    {{ -8,-6,-4,-2,0,2,4,6,0,0 }, { -7,-5,-3,-1,1,3,5,7,0,0 }, 8, -4},
    //28) len=9, odd range
    {{ 0,1,2,3,4,5,6,7,8,0 }, { 0,1,2,3,4,5,6,7,8,0 }, 9, 4},
    //29) len=10, even tens
    {{ 10,20,30,40,50,60,70,80,90,100 },
     {  5,15,25,35,45,55,65,75,85,95 }, 10, 27},
    //30) len=10, even negative mix
    {{ -10,-5,0,5,10,15,20,25,30,35 },
     { -20,-15,-10,-5,0,5,10,15,20,25 }, 10, -5}
};

// Get the number of test cases
int num_tests = sizeof(tests) / sizeof(tests[0]);

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
        int out = FindMedian(tests[i].a, tests[i].b, tests[i].len);

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
        // Print inputs a, b, len
        fprintf(file, "        \"inputs\": {\n");
        fprintf(file, "            \"a\": [");
        for (int j = 0; j < tests[i].len; j++) {
            fprintf(file, "%d", tests[i].a[j]);
            if (j < tests[i].len - 1) fprintf(file, ", ");
        }
        fprintf(file, "],\n");
        fprintf(file, "            \"b\": [");
        for (int j = 0; j < tests[i].len; j++) {
            fprintf(file, "%d", tests[i].b[j]);
            if (j < tests[i].len - 1) fprintf(file, ", ");
        }
        fprintf(file, "],\n");
        fprintf(file, "            \"len\": %d\n", tests[i].len);
        fprintf(file, "        },\n");
        fprintf(file, "        \"expected_output\": %d,\n", tests[i].out);
        fprintf(file, "        \"received_output\": %d,\n", out);
        fprintf(file, "        \"passed\": %s\n",
                (out == tests[i].out) ? "true" : "false");
        fprintf(file, "    },\n");
    }

    // Summary
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
