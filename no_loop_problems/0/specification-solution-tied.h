/*
    One day Vasya the Hipster decided to count how many socks he had. It turned out that he had a red socks and b blue socks. According to the latest fashion, hipsters should wear the socks of different colors: a red one on the left foot, a blue one on the right foot. Every day Vasya puts on new socks in the morning and throws them away before going to bed as he doesn't want to wash them. Vasya wonders, what is the maximum number of days when he can dress fashionable and wear different socks, and after that, for how many days he can then wear the same socks until he either runs out of socks or cannot make a single pair from the socks he's got. Can you help him?

    Input
    The input contains two positive integers a and b ( 1 ≤ a , b ≤ 100 ) — the number of red and blue socks that Vasya's got.

    Output
    Two space-separated integers — the maximum number of days when Vasya can wear different socks and the number of days when he can wear the same socks until he either runs out of socks or cannot make a single pair from the socks he's got. Keep in mind that at the end of the day Vasya throws away the socks that he's been wearing on that day.
*/

/*@
    requires \valid(out1) && \valid(out2) && \separated(out1, out2);
    requires 1 <= a <= 100;
    requires 1 <= b <= 100;
    assigns *out1, *out2;
    behavior has_more_red:
        assumes a > b;
        ensures *out1 == b && *out2 == (a - b) / 2;
    behavior has_more_blue:
        assumes b > a;
        ensures *out1 == a && *out2 == (b - a) / 2;
    behavior equal_socks:
        assumes a == b;
        ensures *out1 == a && *out2 == 0;
    complete behaviors;
    disjoint behaviors;
*/
void calculateHipsterSockDays(int a, int b, int *out1, int *out2);