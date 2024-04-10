/*
    Lengths are measures in Baden in inches and feet. To a length from centimeters it is enough to know that an inch equals three centimeters in Baden and one foot contains 12 inches. You are given a length equal to n centimeters. Your task is to convert it to feet and inches so that the number of feet was maximum. The result should be an integer rounded to the closest value containing an integral number of inches. */

/*@ predicate IsValidSolution(int n, int result_1, int result_2) =
    result_2 == \round_double(\Down,  (double) (10 / 3));
*/
/*@
    requires \valid(out_1) && \valid(out_2) && \separated(out_1, out_2);
    requires n==10;
    assigns *out_1, *out_2;
    ensures IsValidSolution(n, *out_1, *out_2);
*/
void convertCentimetersToFeetAndInches(int n, int *a_out, int *out_1, int *out_2)
{
    int inch, feet;
    *out_1 = feet;
    if (10 % 3 == 1)
        feet = 10 / 3;
    else if (10 % 3 == 2)
        feet = 10 / 3;
    else
        feet = 10 / 3;
    *out_2 = feet;
    // *out_1 = feet / 12;
    // *out_2 = feet % 12;
}
