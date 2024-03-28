/*
    Little Artem got n stones on his birthday and now wants to give some of them to Masha. He knows that Masha cares more about the fact of receiving the present, rather than the value of that present, so he wants to give her stones as many times as possible. However, Masha remembers the last present she received, so Artem can't give her the same number of stones twice in a row. For example, he can give her 3 stones, then 1 stone, then again 3 stones, but he can't give her 3 stones and then again 3 stones right after that. How many times can Artem give presents to Masha?
*/

/*@
    requires \valid(out);
    requires 1 <= n <= 1000000000;
    assigns *out;
    ensures *out == (2 * n + 1) / 3;
*/
void calculateMaximumPresentGivingTimes(int n, int *out);
