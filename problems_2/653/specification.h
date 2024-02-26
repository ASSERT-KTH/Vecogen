/*  Measuring Lengths in Baden
    Lengths are measures in Baden in inches and feet. To a length from centimeters it is enough to know that an inch equals three centimeters in Baden and one foot contains 12 inches. You are given a length equal to n centimeters. Your task is to convert it to feet and inches so that the number of feet was maximum. The result should be an integer rounded to the closest value containing an integral number of inches. */

/*@
    requires 1 <= n <= 10000;
    assigns \nothing;
    behavior feet_rounded_up:
        assumes (n / 3) % 3 == 2;
        ensures \result == ((n / 3) + 1) / 12;
    behavior feet_rounded_down:
        assumes (n / 3) % 3 != 2;
        ensures \result == (n / 3) % 12;
*/
int problem_1(int n);

/*@
    requires 1 <= n <= 10000;
    assigns \nothing;
    behavior feet_rounded_up:
        assumes (n / 3) % 3 == 2;
        ensures \result == ((n / 3) + 1) % 12;
    behavior feet_rounded_down:
        assumes (n / 3) % 3 != 2;
        ensures \result == (n / 3) % 12;
*/
int problem_2(int n);