
#include <stdio.h>

#define HASHTBL_LEN 17

typedef struct {
    int b;
    int size;
} Buckets;

typedef struct {
    Buckets data[HASHTBL_LEN];
    int size;
} Hashtbl;

/* Function declaration */
int add(Hashtbl *tbl, int d);

/* A structure for the test cases */
typedef struct {
    int x;   /* the bucket index d */
    int out; /* expected return value */
} TestCase;

/* Initialize test cases */
TestCase tests[] = {
    { 0, 0}, { 1, 0}, { 2, 0}, { 3, 0}, { 4, 0},
    { 5, 0}, { 6, 0}, { 7, 0}, { 8, 0}, { 9, 0},
    {10, 0}, {11, 0}, {12, 0}, {13, 0}, {14, 0},
    {15, 0}, {16, 0},
    /* repeat some indices to reach 30 cases */
    { 0, 0}, { 1, 0}, { 2, 0}, { 3, 0}, { 4, 0},
    { 5, 0}, { 6, 0}, { 7, 0}, { 8, 0}, { 9, 0},
    {10, 0}, {11, 0}, {12, 0}
};

/* Get the number of test cases */
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
        int out;
        Hashtbl tbl;

        /* initialize the table with non-zero sizes */
        for (int j = 0; j < HASHTBL_LEN; j++) {
            tbl.data[j].size = j + 1;  /* any non-zero */
            tbl.data[j].b = 0;
        }
        tbl.size = HASHTBL_LEN + 5;

        /* Run the function */
        out = add(&tbl, tests[i].x);

        if (out == tests[i].out)
        {
            passed++;
            printf("Test %d passed\n", i + 1);
        }
        else
        {
            printf("Test %d failed\n", i + 1);
        }

        /* Print results as JSON */
        fprintf(file, "    {\n");
        fprintf(file, "        \"test_case\": %d,\n", i + 1);
        fprintf(file, "        \"inputs\": {\"x\": %d},\n", tests[i].x);
        fprintf(file, "        \"expected_output\": %d,\n", tests[i].out);
        fprintf(file, "        \"received_output\": %d,\n", out);
        fprintf(file, "        \"passed\": %s\n", (out == tests[i].out) ? "true" : "false");
        fprintf(file, "    },\n");
    }

    /* summary */
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
