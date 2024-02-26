
/*@
    requires 1 <= N <= 1000000000;
    assigns \nothing;
    behavior odd:
        assumes N % 2 == 0;
        ensures \result == (N / 2);
    behavior even:
        assumes N % 2 == 1;
        ensures \result == (N / 2) + 1;
*/
int problem(int N)
{
    long long result;
    if ((N / 2) % 2 == 0)
    {
        return result;
    }
    else
        return result + 1;
}

#include <stdio.h>
#include <conio.h>
int main()
{
    long long n;
    scanf("%I64d", &n);
    long long result;
    result = n / 2;
    if (n % 2 == 0)
    {
        printf("%I64d", result);
    }
    else
        printf("%I64d", result + 1);
}
'
