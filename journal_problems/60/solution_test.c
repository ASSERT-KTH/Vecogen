#include <stdio.h>

// The function declaration
int beats_card(char trump, char card1[2], char card2[2]);

// A structure for the test cases
typedef struct
{
    int trump;
    char card1[3];
    char card2[3];
    int out;
} TestCase;

// Initialize test cases
TestCase tests[] = {
    {'H', "QH", "9S", 1},
    {'S', "8D", "6D", 1},
    {'C', "7H", "AS", 0},
    {'C', "KC", "9C", 1},
    {'D', "7D", "KD", 0},
    {'H', "7H", "KD", 1},
    {'D', "AS", "AH", 0},
    {'H', "KH", "KS", 1},
    {'C', "9H", "6C", 0},
    {'C', "9H", "JC", 0},
    {'D', "TD", "JD", 0},
    {'H', "6S", "7S", 0},
    {'D', "7S", "8S", 0},
    {'S', "8H", "9H", 0},
    {'C', "9D", "TD", 0},
    {'H', "TC", "JC", 0},
    {'C', "JH", "QH", 0},
    {'H', "QD", "KD", 0},
    {'D', "KS", "AS", 0},
    {'S', "AH", "6H", 1},
    {'H', "7D", "6D", 1},
    {'S', "8H", "7H", 1},
    {'D', "9S", "8S", 1},
    {'S', "TC", "9C", 1},
    {'H', "JS", "TS", 1},
    {'S', "QD", "JD", 1},
    {'D', "KH", "QH", 1},
    {'H', "AD", "KD", 1},
    {'H', "QS", "QD", 0},
    {'C', "TS", "TH", 0},
    {'C', "6C", "6D", 1},
    {'H', "8H", "8D", 1},
    {'S', "7D", "7S", 0},
    {'H', "JC", "JH", 0},
    {'H', "8H", "9C", 1},
    {'D', "9D", "6S", 1},
    {'C', "JC", "AH", 1},
    {'S', "AS", "KD", 1},
    {'S', "7S", "JS", 0},
    {'H', "TH", "8H", 1},
    {'S', "7S", "QS", 0},
    {'C', "KC", "QC", 1},
    {'S', "AD", "9S", 0},
    {'D', "7H", "8D", 0},
    {'H', "JC", "9H", 0},
    {'C', "7S", "AC", 0},
    {'C', "8C", "7C", 1},
    {'H', "9D", "8S", 0},
    {'D', "AC", "KS", 0},
    {'H', "8C", "QH", 0},
    {'S', "7S", "TS", 0},
    {'C', "AH", "6S", 0},
    {'S', "KS", "QS", 1},
    {'H', "AC", "QC", 1},
    {'S', "9H", "8D", 0},
    {'S', "TS", "JS", 0},
    {'S', "8H", "7C", 0},
    {'C', "AH", "6S", 0},
    {'S', "7S", "QS", 0},
    {'C', "AH", "6S", 0},
    {'S', "TS", "KS", 0},
    {'C', "TH", "KH", 0},
    {'H', "9C", "6D", 0},
    {'H', "9C", "8D", 0},
    {'H', "TH", "AH", 0},
    {'H', "TH", "JH", 0},
    {'H', "QS", "9C", 0},
    {'H', "KC", "AC", 0},
    {'H', "AH", "KH", 1},
    {'H', "KS", "QS", 1},
    {'C', "AD", "KS", 0},
    {'H', "QS", "9C", 0},
    {'H', "9D", "7S", 0},
    {'D', "6D", "9S", 1},
    {'H', "AH", "KH", 1},
    {'H', "KC", "AC", 0},
    {'D', "8S", "6C", 0},
    {'S', "AC", "KC", 1}};

// Get the number of test cases
int num_tests = sizeof(tests) / sizeof(tests[0]);

// The main function
int main(int argc, char *argv[])
{
    if (argc < 2)
    {
        printf("Usage: %s <output_filename>\n", argv[0]);
        return 1; // Exit with error code if 0 filename is provided
    }

    // File name is taken from command line
    const char *filename = argv[1];

    // Keep track of the amount of passed tests
    int passed = 0;
    FILE *file = fopen(filename, "w"); // Open the file specified by command line for writing

    if (file == NULL)
    {
        printf("Failed to open file: %s\n", filename);
        return 1; // Exit with error code if file can0t be opened
    }

    // Start JSON array
    fprintf(file, "[\n");

    // For each test case try the function
    for (int i = 0; i < num_tests; i++)
    {
        // Create variables to store the output
        int out;

        // Run the function
        out = beats_card(tests[i].trump, tests[i].card1, tests[i].card2);

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
        fprintf(file, "        \"input\": {\n");
        fprintf(file, "            \"trump\": \"%c\",\n", tests[i].trump);
        fprintf(file, "            \"card1\": \"%s\",\n", tests[i].card1);
        fprintf(file, "            \"card2\": \"%s\"\n", tests[i].card2);
        fprintf(file, "        },\n");
        fprintf(file, "        \"expected_output\": %d,\n", tests[i].out);
        fprintf(file, "        \"received_output\": %d,\n", out);
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