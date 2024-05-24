/*
    Little Elephant loves magic squares very much. A magic square is a 3 × 3 table, each cell contains some positive integer. At that the sums of integers in all rows, columns and diagonals of the table are equal. The figure below shows the magic square, the sum of integers in all its rows, columns and diagonals equals 15. The Little Elephant remembered one magic square. He started writing this square on a piece of paper, but as he wrote, he forgot all three elements of the main diagonal of the magic square. Fortunately, the Little Elephant clearly remembered that all elements of the magic square did not exceed 10^5 . Help the Little Elephant, restore the original magic square, given the Elephant's notes.

    Input
    The first three lines of the input contain the Little Elephant's notes. The first line contains elements of the first row of the magic square. The second line contains the elements of the second row, the third line is for the third row. The main diagonal elements that have been forgotten by the Elephant are represented by zeroes. It is guaranteed that the notes contain exactly three zeroes and they are all located on the main diagonal. It is guaranteed that all positive numbers in the table do not exceed 10^5.

    Output
    Output nine values representing the grid — the Little Elephant's magic square. If there are multiple magic squares, you are allowed to print any of them.

    Note
    that all numbers you print must be positive and not exceed 10^5 . It is guaranteed that there exists at least one magic square that meets the conditions.
*/

/*@ predicate ExistsSolution(integer b, integer c, integer d, integer f, integer g, integer h) =
    \exists integer a, e, i;
    0 <= a <= 100000 && 0 <= e <= 100000 && 0 <= i <= 100000 &&
    a + b + c == a + d + g && a + b + c == b + e + h && a + b + c == c + f + i &&
    a + b + c == a + e + i && a + b + c == c + e + g && a + b + c == d + e + f &&
    a + b + c == d + e + f && a + b + c == g + h + i;

*/

/*@
    requires \valid(out_a) && \valid(out_b) && \valid(out_c);
    requires \valid(out_d) && \valid(out_e) && \valid(out_f);
    requires \valid(out_g) && \valid(out_h) && \valid(out_i);
    requires \separated(out_a, out_b, out_c, out_d, out_e, out_f, out_g, out_h, out_i);
    requires a == 0 && e == 0 && i == 0;
    requires 1 <= b <= 100000 && 1 <= c <= 100000 && 1 <= d <= 100000;
    requires 1 <= f <= 100000 && 1 <= g <= 100000 && 1 <= h <= 100000;
    requires ExistsSolution(b, c, d, f, g, h);
    assigns *out_a, *out_b, *out_c, *out_d, *out_e, *out_f, *out_g, *out_h, *out_i;
    ensures * out_a == (int) (a + b + c + d + e + f + g + h + i) / 2 - b - c;
    ensures * out_b == b;
    ensures * out_c == c;
    ensures * out_d == d;
    ensures * out_e == (int) (a + b + c + d + e + f + g + h + i) / 2 - d - f;
    ensures * out_f == f;
    ensures * out_g == g;
    ensures * out_h == h;
    ensures * out_i == (int) (a + b + c + d + e + f + g + h + i) / 2 - h - g;
*/
void restoreMagicSquare(int a, int b, int c, int d, int e, int f, int g, int h, int i, int *out_a, int *out_b, int *out_c, int *out_d, int *out_e, int *out_f, int *out_g, int *out_h, int *out_i);