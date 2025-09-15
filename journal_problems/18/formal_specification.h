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
requires 1 <= month && month <= 12;
  assigns  \nothing;
  ensures  \result <==> MonthTable(month) == 31;
@
*/

