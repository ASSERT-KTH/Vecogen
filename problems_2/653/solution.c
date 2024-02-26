/*  Measuring Lengths in Baden
    Lengths are measures in Baden in inches and feet. To a length from centimeters it is enough to know that an inch equals three centimeters in Baden and one foot contains 12 inches. You are given a length equal to n centimeters. Your task is to convert it to feet and inches so that the number of feet was maximum. The result should be an integer rounded to the closest value containing an integral number of inches. */

/*@
    requires 1 <= n <= 10000;
    requires \valid(a_out) && \valid(b_out);
    assigns *a_out, *b_out;
    behavior feet_rounded_up:
        assumes n % 3 == 2;
        ensures (*a_out == ((n + 1) / 3) / 12) && (*b_out == ((n + 1) / 3) % 12);
    behavior feet_rounded_down:
        assumes n % 3 == 1;
        ensures (*a_out == ((n - 1) / 3) / 12) && (*b_out == ((n - 1) / 3 ) % 12);
    behavior feet_rounded:
        assumes n % 3 == 0;
        ensures (*a_out == ((n / 3) / 12)) && (*b_out == ((n / 3) % 12));
*/
int problem(int n, int *a_out, int *b_out)
{
    int feet;
    if (n % 3 == 1)
        feet = (n - 1) / 3;
    if (n % 3 == 2)
        feet = (n + 1) / 3;
    else
        feet = n / 3;
    *a_out = feet / 12;
    *b_out = feet % 12;
    return 0;
}
