
#include <stdio.h>
#include <limits.h>

// The function declaration
int CountMonthsWith31Days(int month);

// A structure for the test cases
typedef struct {
    int x;    // input month
    int out;  // expected output
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {   0,  0 },
    {   1,  1 },
    {   2,  1 },
    {   3,  2 },
    {   4,  2 },
    {   5,  3 },
    {   6,  3 },
    {   7,  4 },
    {   8,  5 },
    {   9,  5 },
    {  10,  6 },
    {  11,  6 },
    {  12,  7 },
    {  13,  8 },
    {  14,  8 },
    {  15,  9 },
    {  16,  9 },
    {  17, 10 },
    {  18, 10 },  // corrected
    {  19, 11 },
    {  20, 12 },
    {  30, 17 },
    {  31, 18 },
    { 100, 58 },
    { 365, 213 }, // corrected
    {1000, 583 },
    {100000, 58333 },
    {1234523, 720138 }, // corrected
    {1000000, 583333 },
    {INT_MAX, (INT_MAX/12)*7 + ( (INT_MAX%12==0)?0:
      (INT_MAX%12==1?1:(INT_MAX%12==2?1:(INT_MAX%12==3?2:(INT_MAX%12==4?2:(INT_MAX%12==5?3:
      (INT_MAX%12==6?3:(INT_MAX%12==7?4:(INT_MAX%12==8?5:(INT_MAX%12==9?5:
      (INT_MAX%12==10?6:6))))))))))) }
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
        out = CountMonthsWith31Days(tests[i].x);

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
