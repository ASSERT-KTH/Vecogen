/*
    Today is Wednesday, the third day of the week. What's more interesting is that tomorrow is the last day of the year 2015. Limak is a little polar bear. He enjoyed this year a lot. Now, he is so eager to the coming year 2016. Limak wants to prove how responsible a bear he is. He is going to regularly save candies for the entire year 2016! He considers various saving plans. He can save one candy either on some fixed day of the week or on some fixed day of the month. Limak chose one particular plan. He isn't sure how many candies he will save in the 2016 with his plan. Please, calculate it and tell him.

    Input
    The only two inputs are of the following format:
    Two integers x and mode (1 ≤ x ≤ 31, 0 ≤ mode ≤ 1) — the day of the month and the mode of saving candies. If mode equals 0, then Limak will save candies on the x-th day of the week. If mode equals 1, then Limak will save candies on the x-th day of the month. The week starts with Monday and ends with Sunday.

    Output
    Output one integer — the number of candies Limak will save in the year 2016.
*/

/*@
    requires \valid(out);
    // If the mode is 0, then it is week, if it is 1, then it is month
    requires mode == 0 || mode == 1;
    requires (mode == 0 ==> x >= 1 && x <= 7) && (mode == 1 ==> x >= 1 && x <= 31);
    assigns *out;
    behavior week:
        assumes mode == 0;
        ensures *out == 52 + ((x == 5 || x == 6) ? 1 : 0);
    behavior month:
        assumes mode == 1;
        ensures *out == 12 - ((x > 29) ? 1 : 0) - 4 * ((x > 30) ? 1 : 0);
    complete behaviors;
    disjoint behaviors;
*/
void calculateCandiesSaved(int x, int mode, int *out);