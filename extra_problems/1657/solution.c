#include <stdio.h>
/*
    It is known that fleas in Berland can jump only vertically and horizontally, and the length of the jump is always equal to s centimeters. A flea has found herself at the center of some cell of the checked board of the size n × m centimeters (each cell is 1 × 1 centimeters). She can jump as she wishes for an arbitrary number of times, she can even visit a cell more than once. The only restriction is that she cannot jump out of the board. The flea can count the amount of cells that she can reach from the starting position ( x , y ) . Let's denote this amount by d(x, y). Your task is to find the number of such starting positions ( x , y ) , which have the maximum possible value of d(x, y).
*/

/*@
    requires 1 <= n <= 100;
    requires 1 <= m <= 100;
    requires 1 <= s <= 100;
    requires \valid(out);
    assigns *out;
    ensures (long long int)  *out == (long long int) ((m - 1) / s + 1) * ((m - 1) % s + 1) * ((n - 1) / s + 1) * ((n - 1) % s + 1);
*/
void maxCells(int n, int m, int s, long long int *out)
{
    long long int nn = (n - 1) / s + 1;
    long long int mm = (m - 1) / s + 1;
    long long int nn2 = (n - 1) % s + 1;
    long long int mm2 = (m - 1) % s + 1;
    *out = nn * nn2 * mm * mm2;
}
