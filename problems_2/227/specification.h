/*  Iterated Linear Function
    Consider a linear function f ( x ) = Ax + B . Let's define g (0) ( x ) = x and g ( n ) ( x ) = f ( g ( n - 1) ( x )) for n > 0 . For the given integer values A , B , n and x find the value of g ( n ) ( x ) modulo 10 9 + 7 .
*/

/*@
    requires \valid(out);
    requires 1 <= A <= 1000000000;
    requires 1 <= B <= 1000000000;
    requires 1 <= x <= 1000000000;
    requires 1 <= n <= 1000000000000000000;
    assigns *out;
    ensures *out == g ( n ) ( x ) % 1000000007;
*/
int problem(int A, int B, long long n, int x, int *out);