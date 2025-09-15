
#include <stdio.h>

// The function declaration
int sumTo(int *a, int start, int end, int len);

// A structure for the test cases
typedef struct {
    int a[10];    // array of up to 10 elements
    int len;      // actual length of the array
    int start;
    int end;
    int out;      // expected output
} TestCase;

// Initialize test cases
TestCase tests[] = {
    // 1: empty array
    { .a = {0}, .len = 0, .start = 0, .end = 0, .out = 0 },
    // 2-4: single‐element array [5]
    { .a = {5}, .len = 1, .start = 0, .end = 0, .out = 0 },
    { .a = {5}, .len = 1, .start = 0, .end = 1, .out = 5 },
    { .a = {5}, .len = 1, .start = 1, .end = 1, .out = 0 },
    // 5-9: array [1,2,3]
    { .a = {1,2,3}, .len = 3, .start = 0, .end = 3, .out = 6 },
    { .a = {1,2,3}, .len = 3, .start = 0, .end = 1, .out = 1 },
    { .a = {1,2,3}, .len = 3, .start = 1, .end = 3, .out = 5 },
    { .a = {1,2,3}, .len = 3, .start = 2, .end = 3, .out = 3 },
    { .a = {1,2,3}, .len = 3, .start = 3, .end = 3, .out = 0 },
    // 10-11: zeros array
    { .a = {0,0,0,0}, .len = 4, .start = 0, .end = 4, .out = 0 },
    { .a = {0,0,0,0}, .len = 4, .start = 1, .end = 3, .out = 0 },
    // 12-13: mixed 100's
    { .a = {100,100,100}, .len = 3, .start = 0, .end = 3, .out = 300 },
    { .a = {100,50,0,25}, .len = 4, .start = 2, .end = 4, .out = 25 },
    // 14-15: increasing multiples
    { .a = {10,20,30,40,50}, .len = 5, .start = 1, .end = 4, .out = 20+30+40 },
    { .a = {7,14,21,28,35}, .len = 5, .start = 2, .end = 5, .out = 21+28+35 },
    // 16-17: all ones
    { .a = {1,1,1,1,1}, .len = 5, .start = 0, .end = 5, .out = 5 },
    { .a = {1,1,1,1,1}, .len = 5, .start = 2, .end = 4, .out = 2 },
    // 18: alternating 3 and 0
    { .a = {3,0,3,0,3}, .len = 5, .start = 1, .end = 5, .out = 0+3+0+3 },
    // 19: even numbers
    { .a = {2,4,6,8,10,12}, .len = 6, .start = 3, .end = 6, .out = 8+10+12 },
    // 20-21: descending
    { .a = {9,8,7,6,5}, .len = 5, .start = 0, .end = 2, .out = 9+8 },
    { .a = {9,8,7,6,5}, .len = 5, .start = 3, .end = 5, .out = 6+5 },
    // 22-24: single-element edge
    { .a = {100}, .len = 1, .start = 0, .end = 1, .out = 100 },
    { .a = {100}, .len = 1, .start = 1, .end = 1, .out = 0 },
    { .a = {0}, .len = 1, .start = 0, .end = 1, .out = 0 },
    // 25-29: ten elements
    { .a = {1,2,3,4,5,6,7,8,9,10}, .len = 10, .start = 0, .end = 10, .out = 55 },
    { .a = {1,2,3,4,5,6,7,8,9,10}, .len = 10, .start = 3, .end = 7, .out = 4+5+6+7 },
    { .a = {1,2,3,4,5,6,7,8,9,10}, .len = 10, .start = 9, .end = 10, .out = 10 },
    { .a = {1,2,3,4,5,6,7,8,9,10}, .len = 10, .start = 4, .end = 4, .out = 0 },
    // 30: another small
    { .a = {5,10,15,20}, .len = 4, .start = 0, .end = 4, .out = 5+10+15+20 }
};

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
        out = sumTo(tests[i].a, tests[i].start, tests[i].end, tests[i].len);

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
        // print inputs object
        fprintf(file, "        \"inputs\": {\n");
        fprintf(file, "            \"a\": [");
        for (int j = 0; j < tests[i].len; j++) {
            fprintf(file, "%d", tests[i].a[j]);
            if (j < tests[i].len - 1) fprintf(file, ", ");
        }
        fprintf(file, "],\n");
        fprintf(file, "            \"len\": %d,\n", tests[i].len);
        fprintf(file, "            \"start\": %d,\n", tests[i].start);
        fprintf(file, "            \"end\": %d\n", tests[i].end);
        fprintf(file, "        },\n");
        fprintf(file, "        \"expected_output\": %d,\n", tests[i].out);
        fprintf(file, "        \"received_output\": %d,\n", out);
        fprintf(file, "        \"passed\": %s\n", (out == tests[i].out) ? "true" : "false");
        fprintf(file, "    },\n");
    }

    fprintf(file, "    {\n");
    fprintf(file, "        \"summary\": {\n");
    fprintf(file, "            \"total\": %d,\n", num_tests);
    fprintf(file, "            \"passed\": %d,\n", passed);
    fprintf(file, "            \"failed\": %d,\n", num_tests - passed);
    fprintf(file, "            \"pass_rate\": %.2f\n", (float)passed / num_tests);
    fprintf(file, "        }\n");
    fprintf(file, "    }\n");

    fprintf(file, "]\n");
    fclose(file);
    return 0;
}