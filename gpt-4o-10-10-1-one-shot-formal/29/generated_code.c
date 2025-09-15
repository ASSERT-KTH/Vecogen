#include <stdbool.h>

/*In a system where months of the year are represented numerically, the goal is to determine 
  whether a given month has 30 days. The months are represented by integers ranging from 1 
  to 12, where each integer corresponds to a specific month of the year.

  Input
  The function accepts a single integer input, referred to as "month," which must be between 
  1 and 12, inclusive, representing the months of January through December.

  Output
  The function returns a boolean value indicating whether the specified month has 30 days. 
  The output will be true if the month has 30 days, and false otherwise.
*/

/*@
logic integer MonthTable(integer month) =
    month == 1  ? 31 :
    month == 2  ? 28 :
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
*/

/*@
requires 1 <= month <= 12;
  assigns \nothing;
  ensures \result <==> MonthTable(month) == 30;
@
*/

bool is_month_with_30_days(int month) {
    return (month == 4 || month == 6 || month == 9 || month == 11);
}
