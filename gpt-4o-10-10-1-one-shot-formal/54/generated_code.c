struct SockDays {
    int different_days;
    int same_days;
};

struct SockDays result;

/*One day Vasya the Hipster decided to count how many socks he had. It turned out that he had a red socks and b blue socks. According to the latest fashion, hipsters should wear the socks of different colors: a red one on the left foot, a blue one on the right foot. Every day Vasya puts on new socks in the morning and throws them away before going to bed as he doesn't want to wash them. Vasya wonders, what is the maximum number of days when he can dress fashionable and wear different socks, and after that, for how many days he can then wear the same socks until he either runs out of socks or cannot make a single pair from the socks he's got. Can you help him?

    Input
    The input contains two positive integers a and b (1 <= a , b <= 100) — the number of red and blue socks that Vasya's got.

    Output
    Two space-separated integers — the maximum number of days when Vasya can wear different socks and the number of days when he can wear the same socks until he either runs out of socks or cannot make a single pair from the socks he's got. Keep in mind that at the end of the day Vasya throws away the socks that he's been wearing on that day.
*/

/*@
predicate IsPossibleConfiguration(integer a, integer b, integer result_1, integer result_2) =
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

/*@
predicate ExistsBiggerSolution(integer a, integer b, integer result_1, integer result_2) =
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
requires 1 <= a <= 100;
    requires 1 <= b <= 100;
    assigns \nothing;
    ensures IsPossibleConfiguration(a, b, \result.different_days, \result.same_days);
    ensures !ExistsBiggerSolution(a, b, \result.different_days, \result.same_days);
*/

struct SockDays calculateHipsterSockDays(int a, int b) {
    struct SockDays result;
    if (a < b) {
        int temp = a;
        a = b;
        b = temp;
    }
    if (a - b >= 2) {
        result.different_days = b;
        result.same_days = (a - b) / 2;
    } else if (a == b) {
        result.different_days = a;
        result.same_days = 0;
    } else { // a - b == 1
        result.different_days = b;
        result.same_days = 0;
    }
    return result;
}
