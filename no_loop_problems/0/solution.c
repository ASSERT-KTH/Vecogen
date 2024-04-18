/*
    One day Vasya the Hipster decided to count how many socks he had. It turned out that he had a red socks and b blue socks. According to the latest fashion, hipsters should wear the socks of different colors: a red one on the left foot, a blue one on the right foot. Every day Vasya puts on new socks in the morning and throws them away before going to bed as he doesn't want to wash them. Vasya wonders, what is the maximum number of days when he can dress fashionable and wear different socks, and after that, for how many days he can then wear the same socks until he either runs out of socks or cannot make a single pair from the socks he's got. Can you help him?
*/

// Predicate that looks if the solution is valid
/*@ predicate IsPossibleConfiguration(integer a, integer b, integer result_1, integer result_2) =
    \exists integer naa, nab, nbb, a_rem, b_rem;
    0 <= naa <= a / 2 &&
    0 <= nab <= (a + b) / 2 &&
    0 <= nbb <= b / 2 &&
    0 <= a_rem <= 1 &&
    0 <= b_rem <= 1 &&
    2 * naa + nab + a_rem == a &&
    2 * nbb + nab + b_rem == b &&
    a_rem + b_rem <= 1 &&
    result_1 == nab && result_2 == naa + nbb;
*/

// Predicate that shows that there does not exist a solution with a higher value
/*@ predicate ExistsBiggerSolution(integer a, integer b, integer result_1, integer result_2) =
    \exists integer naa, nab, nbb, a_rem, b_rem;
    0 <= naa <= a / 2 &&
    0 <= nab <= (a + b) / 2 &&
    0 <= nbb <= b / 2 &&
    0 <= a_rem <= 1 &&
    0 <= b_rem <= 1 &&
    2 * naa + nab + a_rem == a &&
    2 * nbb + nab + b_rem == b &&
    nab > result_1 && result_2 == naa + nbb;
*/

/*@
    requires \valid(out1) && \valid(out2) && \separated(out1, out2);
    requires 1 <= a <= 100;
    requires 1 <= b <= 100;
    assigns *out1, *out2;
    ensures IsPossibleConfiguration(a, b, *out1, *out2);
    ensures !ExistsBiggerSolution(a, b, *out1, *out2);
*/
void calculateHipsterSockDays(int a, int b, int *out1, int *out2)
{
    if (a > b)
    {
        *out1 = b;
        *out2 = (a - b) / 2;
    }
    else if (b > a)
    {
        *out1 = a;
        *out2 = (b - a) / 2;
    }
    else
    {
        *out1 = a;
        *out2 = 0;
    }
}
