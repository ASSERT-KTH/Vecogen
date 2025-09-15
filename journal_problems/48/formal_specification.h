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

