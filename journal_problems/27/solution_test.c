
#include <stdio.h>
#include <stdbool.h>

// The function declaration
bool IsArmstrong(int n);

// A structure for the test cases
typedef struct {
    int x;
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {100, 0},
    {101, 0},
    {111, 0},
    {123, 0},
    {130, 0},
    {153, 1},
    {200, 0},
    {370, 1},
    {371, 1},
    {407, 1},
    {999, 0},
    {998, 0},
    {947, 0},
    {512, 0},
    {125, 0},
    {820, 0},
    {703, 0},
    {764, 0},
    {500, 0},
    {614, 0},
    {728, 0},
    {759, 0},
    {786, 0},
    {980, 0},
    {364, 0},
    {927, 0},
    {930, 0},
    {321, 0},
    {695, 0},
    {135, 0},
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
        out = IsArmstrong(tests[i].x);

        if (out == tests[i].out)
        {
            passed++;
            printf("Test %d passed\n", i + 1);
        }
        else
        {
            printf("Test %d failed\n", i + 1);
        }

        // Print results as JSON
        fprintf(file, "    {\n");
        fprintf(file, "        \"test_case\": %d,\n", i + 1);
        fprintf(file, "        \"inputs\": {\"x\": %d},\n", tests[i].x);
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
