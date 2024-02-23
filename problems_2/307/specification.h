/*  A. Checking the Calendar
    You are given names of two days of the week. Please, determine whether it is possible that during some non-leap year the first day of some month was equal to the first day of the week you are given, while the first day of the next month was equal to the second day of the week you are given. Both months should belong to one year . In this problem, we consider the Gregorian calendar to be used. The number of months in this calendar is equal to 12. The number of days in months during any non-leap year is: 31 , 28 , 31 , 30 , 31 , 30 , 31 , 31 , 30 , 31 , 30 , 31 . Names of the days of the week are given with lowercase English letters: " monday ", " tuesday ", " wednesday ", " thursday ", " friday ", " saturday ", " sunday ". */
/*@
    requires \valid(s1+(0..9));
    requires \valid(s2+(0..9));
    requires \exists integer i; 0 <= i < 7 && s1[0] == \at("monday"[i], Pre);
    requires \exists integer i; 0 <= i < 7 && s2[0] == \at("monday"[i], Pre);
    assigns \nothing;
    ensures \result == 1 || \result == 0;
*/
int problem(char *s1, char *s2);
