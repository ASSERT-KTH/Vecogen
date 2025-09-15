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

