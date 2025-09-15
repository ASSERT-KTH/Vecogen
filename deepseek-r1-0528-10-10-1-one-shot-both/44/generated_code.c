typedef struct {
    int a, b, c;
    int d, e, f;
    int g, h, i;
} magic_square;

/*Little Elephant loves magic squares very much. A magic square is a 3 × 3 table, each cell contains some positive integer. At that the sums of integers in all rows, columns and diagonals of the table are equal. The figure below shows the magic square, the sum of integers in all its rows, columns and diagonals equals 15. The Little Elephant remembered one magic square. He started writing this square on a piece of paper, but as he wrote, he forgot all three elements of the main diagonal of the magic square. Fortunately, the Little Elephant clearly remembered that all elements of the magic square did not exceed 10^5 . Help the Little Elephant, restore the original magic square, given the Elephant's notes.

    Input
    The first three lines of the input contain the Little Elephant's notes. The first line contains elements of the first row of the magic square. The second line contains the elements of the second row, the third line is for the third row. The main diagonal elements that have been forgotten by the Elephant are represented by zeroes. It is guaranteed that the notes contain exactly three zeroes and they are all located on the main diagonal. It is guaranteed that all positive numbers in the table do not exceed 10^5.

    Output
    Output nine values representing the grid — the Little Elephant's magic square. If there are multiple magic squares, you are allowed to print any of them.

    Note
    that all numbers you print must be positive and not exceed 10^5 . It is guaranteed that there exists at least one magic square that meets the conditions.
*/

/*@
predicate ExistsSolution(integer b, integer c, integer d, integer f, integer g, integer h) =
    \exists integer a, e, i;
    0 <= a <= 100000 && 0 <= e <= 100000 && 0 <= i <= 100000 &&
    a + b + c == a + d + g && a + b + c == b + e + h && a + b + c == c + f + i &&
    a + b + c == a + e + i && a + b + c == c + e + g && a + b + c == d + e + f &&
    a + b + c == d + e + f && a + b + c == g + h + i;
*/

/*@
predicate IsValidSolution(integer a, integer b, integer c, integer d, integer e, integer f, integer g, integer h, integer i) =
    \exists integer sum;
    0 <= a <= 100000 && 0 <= b <= 100000 && 0 <= c <= 100000 &&
    0 <= d <= 100000 && 0 <= e <= 100000 && 0 <= f <= 100000 &&
    0 <= g <= 100000 && 0 <= h <= 100000 && 0 <= i <= 100000 &&
    0 <= sum && sum == a + b + c && sum == d + e + f && sum == g + h + i &&
    sum == a + d + g && sum == b + e + h && sum == c + f + i &&
    sum == a + e + i && sum == c + e + g;
*/

/*@
requires a == 0 && e == 0 && i == 0;
    requires 1 <= b <= 100000 && 1 <= c <= 100000 && 1 <= d <= 100000;
    requires 1 <= f <= 100000 && 1 <= g <= 100000 && 1 <= h <= 100000;
    requires ExistsSolution(b, c, d, f, g, h);
    assigns \nothing;
    ensures \result.b == b && \result.c == c && \result.d == d &&
            \result.f == f && \result.g == g && \result.h == h;
    ensures IsValidSolution(\result.a, \result.b, \result.c,
                             \result.d, \result.e, \result.f,
                             \result.g, \result.h, \result.i);
*/

magic_square restoreMagicSquare(int a, int b, int c, int d, int e, int f, int g, int h, int i) {
    magic_square res;
    res.b = b;
    res.c = c;
    res.d = d;
    res.f = f;
    res.g = g;
    res.h = h;
    res.e = (b + h) / 2;
    int S = 3 * res.e;
    res.a = S - b - c;
    res.i = S - g - h;
    return res;
}
