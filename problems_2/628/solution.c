/*  Lucky Division
    Petya loves lucky numbers. Everybody knows that lucky numbers are positive integers whose decimal representation contains only the lucky digits 4 and 7 . For example, numbers 47 , 744 , 4 are lucky and 5 , 17 , 467 are not. Petya calls a number almost lucky if it could be evenly divided by some lucky number. Help him find out if the given number n is almost lucky. */

/*@
    requires \valid(out);
    requires 1 <= n <= 1000;
    assigns *out;
    behavior almost_lucky:
        assumes n % 4 == 0 || n % 7 == 0 || n % 47 == 0;
        ensures *out == 1;
    behavior not_almost_lucky:
        assumes n % 4 != 0 && n % 7 != 0 && n % 47 != 0;
        ensures *out == 0;
*/
void problem(int n, int *out)
{
    *out = n % 4 == 0 || n % 7 == 0 || n % 47 == 0;
}