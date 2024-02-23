
#include <stdio.h>
int main()
{
    int x;
    scanf("%d", &x);
    if (x % 5)
        printf("%d\\n", x / 5 + 1);
    else
        printf("%d\\n", x / 5);
    return 0;
}
