/*
    Lengths are measures in Baden in inches and feet. To a length from centimeters it is enough to know that an inch equals three centimeters in Baden and one foot contains 12 inches. You are given a length equal to n centimeters. Your task is to convert it to feet and inches so that the number of feet was maximum. The result should be an integer rounded to the closest value containing an integral number of inches. */

/*@ predicate isValidSolution(int n, int result_1, int result_2) =
    result_1 == n / 3 &&
    0 == (int) \round_float(\Up, (real) 0.9);
*/

/*@
    requires \valid(out_1) && \valid(out_2) && \separated(out_1, out_2);
    requires 1 <= n <= 10000;
    assigns *out_1, *out_2;
    ensures isValidSolution(n, *out_1, *out_2);
*/
void convertCentimetersToFeetAndInches(int n, int *a_out, int *out_1, int *out_2)
{
    int inch, feet;
    feet = n / 3;
    *out_1 = feet;
    if (n % 3 == 2)
        feet++;

    *out_2 = feet;
    // *out_1 = feet / 12;
    // *out_2 = feet % 12;
}
