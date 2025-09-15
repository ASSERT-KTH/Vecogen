
#include <stdio.h>

// Declarations for the code under test
struct counter {
    int seconds;
    int minutes;
    int hours;
};
extern struct counter c;
void tick(void);

// A structure for the test cases
typedef struct {
    int init_seconds;
    int init_minutes;
    int init_hours;
    int exp_seconds;
    int exp_minutes;
    int exp_hours;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    // Behavior one: seconds < 59, minutes < 59
    {  0,  0,  0,   1,  0,  0 },
    { 10, 20,  5,  11, 20,  5 },
    { 15, 15, 15,  16, 15, 15 },
    { 45, 30, 23,  46, 30, 23 },
    { 58, 58, 23,  59, 58, 23 },

    // Behavior two: seconds == 59, minutes < 59
    { 59,  0,  0,   0,  1,  0 },
    { 59, 45,  5,   0, 46,  5 },
    { 59, 58, 22,   0, 59, 22 },
    { 59,  0, 23,   0,  1, 23 },
    { 59, 59-1,23,  0, 59, 23 },

    // Behavior three: seconds < 59, minutes == 59
    { 30, 59, 10,  31, 59, 10 },
    { 58, 59, 13,  59, 59, 13 },
    {  0, 59,  0,   1, 59,  0 },
    {  0, 59, 23,   1, 59, 23 },
    { 58, 59,  0,  59, 59,  0 },

    // Behavior four: seconds == 59, minutes == 59, hours < 23
    { 59, 59,  0,   0,  0,  1 },
    { 59, 59,  1,   0,  0,  2 },
    { 59, 59, 14,   0,  0, 15 },
    { 59, 59, 17,   0,  0, 18 },
    { 59, 59, 21,   0,  0, 22 },

    // Behavior five: seconds == 59, minutes == 59, hours == 23
    { 59, 59, 23,   0,  0,  0 },

    // Additional edge and random cases
    {  1, 59, 23,   2, 59, 23 },
    { 58,  0,  0,  59,  0,  0 },
    { 59,  0, 23,   0,  1, 23 },
    { 59, 59, 19,   0,  0, 20 },
    { 57, 57, 23,  58, 57, 23 },
    { 59, 59, 15,   0,  0, 16 },
    { 59, 59, 16,   0,  0, 17 },
    { 59, 59,  8,   0,  0,  9 },
    { 20, 20, 20,  21, 20, 20 },
    {  5, 59,  5,   6, 59,  5 },
    { 59, 58, 23,   0, 59, 23 },
    { 45, 45, 22,  46, 45, 22 }
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
        // Set up inputs
        c.seconds = tests[i].init_seconds;
        c.minutes = tests[i].init_minutes;
        c.hours   = tests[i].init_hours;

        // Run the function
        tick();

        // Capture outputs
        int out_s = c.seconds;
        int out_m = c.minutes;
        int out_h = c.hours;

        int ok = (out_s == tests[i].exp_seconds
               && out_m == tests[i].exp_minutes
               && out_h == tests[i].exp_hours);

        if (ok)
        {
            passed++;
            printf("Test %d passed\n", i + 1);
        }
        else
        {
            printf("Test %d failed (got %d:%d:%d, expected %d:%d:%d)\n",
                   i + 1,
                   out_h, out_m, out_s,
                   tests[i].exp_hours,
                   tests[i].exp_minutes,
                   tests[i].exp_seconds);
        }

        // Print results as JSON
        fprintf(file, "    {\n");
        fprintf(file, "        \"test_case\": %d,\n", i + 1);
        fprintf(file, "        \"inputs\": { \"seconds\": %d, \"minutes\": %d, \"hours\": %d },\n",
                tests[i].init_seconds,
                tests[i].init_minutes,
                tests[i].init_hours);
        fprintf(file, "        \"expected_output\": { \"seconds\": %d, \"minutes\": %d, \"hours\": %d },\n",
                tests[i].exp_seconds,
                tests[i].exp_minutes,
                tests[i].exp_hours);
        fprintf(file, "        \"received_output\": { \"seconds\": %d, \"minutes\": %d, \"hours\": %d },\n",
                out_s,
                out_m,
                out_h);
        fprintf(file, "        \"passed\": %s\n", ok ? "true" : "false");
        fprintf(file, "    }%s\n", (i + 1 < num_tests) ? "," : "");
    }

    // Summary
    fprintf(file, "    ,{\n");
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
