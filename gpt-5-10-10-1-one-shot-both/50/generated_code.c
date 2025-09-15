/*Valera the Horse is going to the party with friends. He has been following the fashion trends for a while, and he knows that it is very popular to wear all horseshoes of different color. Valera has got four horseshoes left from the last year, but maybe some of them have the same color. In this case he needs to go to the store and buy some few more horseshoes, not to lose face in front of his stylish comrades. Fortunately, the store sells horseshoes of all colors under the sun and Valera has enough money to buy any four of them. However, in order to save the money, he would like to spend as little money as possible, so you need to help Valera and determine what is the minimum number of horseshoes he needs to buy to wear four horseshoes of different colors to a party.

    Input
    The input contains four integers s1 , s2 , s3 , s4 (1 <= s1 , s2 , s3 , s4 <= 10^9 ) — the colors of horseshoes Valera has. Consider all possible colors indexed with integers.

    Output
    Return a single integer — the minimum number of horseshoes Valera needs to buy.
*/

/*@
logic integer amountOfDifferentNumbers(integer a, integer b, integer c, integer d) =
    1 + (int) (a != b) + (int) (a != c && b != c) + (int) (a != d && b != d && c != d);
*/

/*@
predicate IsValidSolution(integer a, integer b, integer c, integer d, integer out) =
    out + amountOfDifferentNumbers(a, b, c, d) >= 4;
*/

/*@
predicate ExistsSmallerSolution(integer a, integer b, integer c, integer d, integer out) =
    \exists integer unique_colors;
    0 <= unique_colors && unique_colors + amountOfDifferentNumbers(a, b, c, d) >= 4 &&
        unique_colors < out;
*/

/*@
requires 1 <= a <= 1000000000;
    requires 1 <= b <= 1000000000;
    requires 1 <= c <= 1000000000;
    requires 1 <= d <= 1000000000;
    assigns \nothing;
    ensures IsValidSolution(a, b, c, d, \result);
    ensures !ExistsSmallerSolution(a, b, c, d, \result);
*/

int minimumHorseshoesNeeded(int a, int b, int c, int d) {
    int unique = 1
        + ((a != b) ? 1 : 0)
        + (((a != c) && (b != c)) ? 1 : 0)
        + (((a != d) && (b != d) && (c != d)) ? 1 : 0);
    return 4 - unique;
}
