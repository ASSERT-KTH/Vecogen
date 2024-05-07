/*
    Little Elephant loves magic squares very much. A magic square is a 3 × 3 table, each cell contains some positive integer. At that the sums of integers in all rows, columns and diagonals of the table are equal. The figure below shows the magic square, the sum of integers in all its rows, columns and diagonals equals 15. The Little Elephant remembered one magic square. He started writing this square on a piece of paper, but as he wrote, he forgot all three elements of the main diagonal of the magic square. Fortunately, the Little Elephant clearly remembered that all elements of the magic square did not exceed 10 5 . Help the Little Elephant, restore the original magic square, given the Elephant's notes.
*/

/*@ predicate ExistsSolution(integer b, integer c, integer d, integer f, integer g, integer h) =
    \exists integer a, e, i;
    0 <= a <= 100000 && 0 <= e <= 100000 && 0 <= i <= 100000 &&
    a + b + c == a + d + g && a + b + c == b + e + h && a + b + c == c + f + i &&
    a + b + c == a + e + i && a + b + c == c + e + g && a + b + c == d + e + f &&
    a + b + c == d + e + f && a + b + c == g + h + i;

*/
/*@ predicate IsValidSolution(integer a, integer b, integer c, integer d, integer e, integer f, integer g, integer h, integer i) =
    \exists integer sum;
    0 <= a <= 100000 && 0 <= b <= 100000 && 0 <= c <= 100000 &&
    0 <= d <= 100000 && 0 <= e <= 100000 && 0 <= f <= 100000 &&
    0 <= g <= 100000 && 0 <= h <= 100000 && 0 <= i <= 100000 &&
    0 <= sum && sum == a + b + c && sum == d + e + f && sum == g + h + i &&
    sum == a + d + g && sum == b + e + h && sum == c + f + i &&
    sum == a + e + i && sum == c + e + g;
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
    ensures IsValidSolution(*out_a, *out_b, *out_c, *out_d, *out_e, *out_f, *out_g, *out_h, *out_i);
*/
void restoreMagicSquare(int a, int b, int c, int d, int e, int f, int g, int h, int i, int *out_a, int *out_b, int *out_c, int *out_d, int *out_e, int *out_f, int *out_g, int *out_h, int *out_i)
{
    int sum = (a + b + c + d + e + f + g + h + i) / 2;
    *out_a = sum - b - c;
    *out_b = b;
    *out_c = c;
    *out_d = d;
    *out_e = sum - d - f;
    *out_f = f;
    *out_g = g;
    *out_h = h;
    *out_i = sum - h - g;
}