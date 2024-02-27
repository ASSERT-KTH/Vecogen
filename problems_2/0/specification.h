/*  A. Vasya the Hipster
    One day Vasya the Hipster decided to count how many socks he had. It turned out that he had a red socks and b blue socks. According to the latest fashion, hipsters should wear the socks of different colors: a red one on the left foot, a blue one on the right foot. Every day Vasya puts on new socks in the morning and throws them away before going to bed as he doesn't want to wash them. Vasya wonders, what is the maximum number of days when he can dress fashionable and wear different socks, and after that, for how many days he can then wear the same socks until he either runs out of socks or cannot make a single pair from the socks he's got. Can you help him?
*/

/* Computation of the maximal number of days when hhe can dress fashionable and wear different socks */
/*@
    requires \valid(out_1) && \valid(out_2) && \separated(out_1, out_2);
    requires 1 <= a <= 100;
    requires 1 <= b <= 100;
    assigns *out_1, *out_2;
    behavior has_more_red:
        assumes a > b;
        ensures *out_1 == b && *out_2 == (a - b) / 2;
    behavior has_more_blue:
        assumes b > a;
        ensures *out_1 == a && *out_2 == (b - a) / 2;
    behavior equal_socks:
        assumes a == b;
        ensures *out_1 == a && *out_2 == 0;
*/
void problem(int a, int b, int *out_1, int *out_2);