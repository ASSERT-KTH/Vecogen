/*  Measuring Lengths in Baden
    Lengths are measures in Baden in inches and feet. To a length from centimeters it is enough to know that an inch equals three centimeters in Baden and one foot contains 12 inches. You are given a length equal to n centimeters. Your task is to convert it to feet and inches so that the number of feet was maximum. The result should be an integer rounded to the closest value containing an integral number of inches. */

/*@
    requires \valid(out_1) && \valid(out_2) && \separated(out_1, out_2);
    requires 1 <= n <= 10000;
    assigns *out_1, *out_2;
    behavior feet_rounded_up:
        assumes n % 3 == 2;
        ensures *out_1 == ((n / 3) + 1) / 12;
        ensures *out_2 == ((n / 3) + 1) % 12;
    behavior feet_rounded_down:
        assumes n % 3 != 2;
        ensures *out_1 == (n / 3) / 12;
        ensures *out_2 == (n / 3) % 12;
    complete behaviors;
    disjoint behaviors;
*/
void problem(int n, int *a_out, int *out_1, int *out_2)
{
    int inch, feet;
    feet = n / 3;
    if (n % 3 == 2)
        feet++;
    *out_1 = feet / 12;
    *out_2 = feet % 12;
}
