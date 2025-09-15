/*Today is Wednesday, the third day of the week. What's more interesting is that tomorrow is the last day of the year 2015. Limak is a little polar bear. He enjoyed this year a lot. Now, he is so eager to the coming year 2016. Limak wants to prove how responsible a bear he is. He is going to regularly save candies for the entire year 2016! He considers various saving plans. He can save one candy either on some fixed day of the week or on some fixed day of the month. Limak chose one particular plan. He isn't sure how many candies he will save in the 2016 with his plan. Please, calculate it and tell him.

    Input
    The input consists of two integers, one that depicts the day and the second one depicts the mode. The mode refers to either week (mode == 0) or month (mode == 1). The day of the week can be of size ( 1 <= x <= 7 ) denotes the day of the week. The 1-st day is Monday and the 7-th one is Sunday.  The second mode is mode of month,  where day ( 1 <= x <= 31 ) denotes the day of the month.

    Output
    Return one integer — the number of candies Limak will save in the year 2016.
*/

/*@
logic integer num_candies_by_weekday(integer x) =
        366 / 7 + (int) ((x + 2) % 7 < 366 % 7);

    logic integer MonthTable(integer month) =
        month == 1  ? 31 :
        month == 2  ? 29 :
        month == 3  ? 31 :
        month == 4  ? 30 :
        month == 5  ? 31 :
        month == 6  ? 30 :
        month == 7  ? 31 :
        month == 8  ? 31 :
        month == 9  ? 30 :
        month == 10 ? 31 :
        month == 11 ? 30 :
        month == 12 ? 31 :
        0;

    logic integer num_candies_by_monthday(integer month, int n) =
        (month <= 0) ? 0  : (MonthTable(month) >= n ? 1 : 0) + num_candies_by_monthday(month - 1, n);
*/

/*@
requires mode == 0 || mode == 1;
    requires (mode == 0) ==> 1 <= day <= 7;
    requires (mode == 1) ==> 1 <= day <= 31;
    // mode == 0 → weekday mode, mode == 1 → monthday mode
    assigns \nothing;
    ensures (mode == 0) ==> \result == num_candies_by_weekday(day);
    ensures (mode == 1) ==> \result == num_candies_by_monthday(12, day);
*/

int count_candies(int day, int mode) {
    if (mode == 0) {
        return 366 / 7 + ((day + 2) % 7 < 366 % 7 ? 1 : 0);
    }
    else { // mode == 1
        int candies = 0;
        candies += day <= 31 ? 1 : 0; // Jan
        candies += day <= 29 ? 1 : 0; // Feb
        candies += day <= 31 ? 1 : 0; // Mar
        candies += day <= 30 ? 1 : 0; // Apr
        candies += day <= 31 ? 1 : 0; // May
        candies += day <= 30 ? 1 : 0; // Jun
        candies += day <= 31 ? 1 : 0; // Jul
        candies += day <= 31 ? 1 : 0; // Aug
        candies += day <= 30 ? 1 : 0; // Sep
        candies += day <= 31 ? 1 : 0; // Oct
        candies += day <= 30 ? 1 : 0; // Nov
        candies += day <= 31 ? 1 : 0; // Dec
        return candies;
    }
}
