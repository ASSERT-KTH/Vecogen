/*Nikolay has a lemons, b apples and c pears. He decided to cook a compote. According to the recipe the fruits should be in the ratio 1: 2: 4 . It means that for each lemon in the compote should be exactly 2 apples and exactly 4 pears. You can't crumble up, break up or cut these fruits into pieces. These fruits — lemons, apples and pears — should be put in the compote as whole fruits. Your task is to determine the maximum total number of lemons, apples and pears from which Nikolay can cook the compote. It is possible that Nikolay can't use any fruits, in this case print 0 .

    Input
    The input contains a positive integer a (1 <= a <= 1000) — the number of lemons Nikolay has. The second input parameter contains the positive integer b (1 <= b <= 1000) — the number of apples Nikolay has. The third input parameter  contains the positive integer c (1 <= c <= 1000) — the number of pears Nikolay has.

    Output
    Return the maximum total number of lemons, apples and pears from which Nikolay can cook the compote.
*/

/*@
predicate isValidSolution(integer a, integer b, integer c, integer out) =
    \exists integer a_used, b_used, c_used;
    0 <= a_used <= a &&
    0 <= b_used <= b &&
    0 <= c_used <= c &&
    4 * a_used == 2 * b_used == c_used &&
    a_used + b_used + c_used == out;
*/

/*@
predicate existsLargerSolution(integer a, integer b, integer c, integer out) =
    \exists integer a_used, b_used, c_used;
    0 <= a_used <= a &&
    0 <= b_used <= b &&
    0 <= c_used <= c &&
    4 * a_used == 2 * b_used == c_used &&
    a_used + b_used + c_used > out;
*/

/*@
requires 1 <= a <= 1000;
    requires 1 <= b <= 1000;
    requires 1 <= c <= 1000;
    assigns \nothing;
    ensures isValidSolution(a, b, c, \result);
    ensures !existsLargerSolution(a, b, c, \result);
*/

int calculateMaxFruitsForCompote(int a, int b, int c) {
    int max_by_lemons = a;
    int max_by_apples = b / 2;
    int max_by_pears = c / 4;
    
    int max_total_sets = max_by_lemons;
    if (max_by_apples < max_total_sets) {
        max_total_sets = max_by_apples;
    }
    if (max_by_pears < max_total_sets) {
        max_total_sets = max_by_pears;
    }
    
    return max_total_sets * 7;
}
