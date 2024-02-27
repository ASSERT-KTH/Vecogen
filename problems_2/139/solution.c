/*  A. Home Numbers
    The main street of Berland is a straight line with n houses built along it ( n is an even number). The houses are located at both sides of the street. The houses with odd numbers are at one side of the street and are numbered from 1 to n - 1 in the order from the beginning of the street to the end (in the picture: from left to right). The houses with even numbers are at the other side of the street and are numbered from 2 to n in the order from the end of the street to its beginning (in the picture: from right to left). The corresponding houses with even and odd numbers are strictly opposite each other, that is, house 1 is opposite house n , house 3 is opposite house n - 2 , house 5 is opposite house n - 4 and so on. Vasya needs to get to house number a as quickly as possible. He starts driving from the beginning of the street and drives his car to house a . To get from the beginning of the street to houses number 1 and n , he spends exactly 1 second. He also spends exactly one second to drive the distance between two neighbouring houses. Vasya can park at any side of the road, so the distance between the beginning of the street at the houses that stand opposite one another should be considered the same. Your task is: find the minimum time Vasya needs to reach house a .*/

/*@
    requires \valid(out);
    requires 1 <= a <= n <= 100000;
    requires n % 2 == 0;
    assigns *out;
    behavior a_is_even:
        assumes a % 2 == 0;
        ensures *out == 1 + (n - a) / 2;
    behavior a_is_odd:
        assumes a % 2 == 1;
        ensures *out == (a + 1) / 2 ;
*/
void problem(int n, int a, int *out)
{
    if (a % 2 == 0)
    {
        *out = (n / 2) - (a / 2) + 1;
    }
    else
        *out = a / 2 + 1;
}