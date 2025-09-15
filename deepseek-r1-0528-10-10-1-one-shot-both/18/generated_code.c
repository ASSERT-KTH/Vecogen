/*The problem involves determining whether a given month has 31 days. The months are represented by integer values ranging from 1 to 12, where each value corresponds to a specific month of the year.

  Input
  The input is a single integer variable, month, which can take any value from 1 to 12 inclusive.

  Output
  The output is a boolean value indicating whether the specified month has 31 days. The output will be true if the month has 31 days and false otherwise.
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
requires 1 <= month && month <= 12;
  assigns  \nothing;
  ensures  \result <==> MonthTable(month) == 31;
@
*/

int MonthHas31Days(int month) {
    return (month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12);
}
