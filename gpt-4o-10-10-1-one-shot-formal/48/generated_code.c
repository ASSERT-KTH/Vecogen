/*You are given names of two days of the week. Please, determine whether it is possible that during some non-leap year the first day of some month was equal to the first day of the week you are given, while the first day of the next month was equal to the second day of the week you are given. Both months should belong to one year . In this problem, we consider the Gregorian calendar to be used. The number of months in this calendar is equal to 12. The number of days in months during any non-leap year is: 31 , 28 , 31 , 30 , 31 , 30 , 31 , 31 , 30 , 31 , 30 , 31.

    Input
    The input consists of two integers, each representing a week day. 0 refers to monday, 1 to tuesday, 2 to wednesday, 3 to thursday, 4 to friday, 5 to saturday and 6 to sunday. The first integer w1 is the first day of the week, the second integer w2 is the second day of the week. 

    Output
    Return 1 if such situation is possible during some non-leap year. Otherwise, return 0.
*/

/*@
logic integer month_len(integer i) =
        (i == 1)  ? 31
        : (i == 2)  ? 28
        : (i == 3)  ? 30
        : (i == 4)  ? 30
        : (i == 5)  ? 31
        : (i == 6)  ? 30
        : (i == 7)  ? 31
        : (i == 8)  ? 31
        : (i == 9)  ? 30
        : (i ==10)  ? 31
        : (i ==11)  ? 30
        : (i ==12)  ? 31
        :              0;
*/

/*@
requires 0 <= w1 <= 6;
    requires 0 <= w2 <= 6;
    assigns \nothing;
    ensures \result == (
        ((w1 + month_len(1)) % 7 == w2) ||
        ((w1 + month_len(2)) % 7 == w2) ||
        ((w1 + month_len(3)) % 7 == w2) ||
        ((w1 + month_len(4)) % 7 == w2) ||
        ((w1 + month_len(5)) % 7 == w2) ||
        ((w1 + month_len(6)) % 7 == w2) ||
        ((w1 + month_len(7)) % 7 == w2) ||
        ((w1 + month_len(8)) % 7 == w2) ||
        ((w1 + month_len(9)) % 7 == w2) ||
        ((w1 + month_len(10)) % 7 == w2) ||
        ((w1 + month_len(11)) % 7 == w2)
    ) ? 1 : 0;
*/

int months_transition(int w1, int w2) {
    return ((w1 + 31) % 7 == w2 || 
            (w1 + 28) % 7 == w2 || 
            (w1 + 30) % 7 == w2 || 
            (w1 + 30) % 7 == w2 || 
            (w1 + 31) % 7 == w2 || 
            (w1 + 30) % 7 == w2 || 
            (w1 + 31) % 7 == w2 || 
            (w1 + 31) % 7 == w2 || 
            (w1 + 30) % 7 == w2 || 
            (w1 + 31) % 7 == w2 || 
            (w1 + 30) % 7 == w2) ? 1 : 0;
}
