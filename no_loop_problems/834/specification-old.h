/*
    Some country is populated by wizards. They want to organize a demonstration. There are n people living in the city, x of them are the wizards who will surely go to the demonstration. Other city people ( n - x people) do not support the wizards and aren't going to go to the demonstration. We know that the city administration will react only to the demonstration involving at least y percent of the city people. Having considered the matter, the wizards decided to create clone puppets which can substitute the city people on the demonstration. So all in all, the demonstration will involve only the wizards and their puppets. The city administration cannot tell the difference between a puppet and a person, so, as they calculate the percentage, the administration will consider the city to be consisting of only n people and not containing any clone puppets. Help the wizards and find the minimum number of clones to create to that the demonstration had no less than y percent of the city people.
 */

/*@
    requires \valid(out);
    requires 1 <= x <= 10000;
    requires 1 <= y <= 10000;
    requires 1 <= n <= 10000;
    requires  x <= n;
    assigns *out;
    behavior zero_clones:
        assumes (n * y + 99) / 100 - x <= 0;
        ensures *out == 0;
    behavior positive_clones:
        assumes (n * y + 99) / 100 - x > 0;
        ensures *out == (n * y + 99) / 100 - x;
    complete behaviors;
    disjoint behaviors;
*/
void calculateMinimumClonesForDemonstrationPercentage(int n, int x, int y, int *out);