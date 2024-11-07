/*
    A. Toy Army time
        The hero of our story, Valera, and his best friend Arcady are still in school, and therefore they spend all the free time playing turn-based strategy "GAGA: Go And Go Again". The gameplay is as follows. There are two armies on the playing field each of which consists of n men ( n is always even). The current player specifies for each of her soldiers an enemy's soldier he will shoot (a target) and then all the player's soldiers shot simultaneously. This is a game world, and so each soldier shoots perfectly, that is he absolutely always hits the specified target. If an enemy soldier is hit, he will surely die. It may happen that several soldiers had been indicated the same target. Killed soldiers do not participate in the game anymore. The game "GAGA" consists of three steps: first Valera makes a move, then Arcady, then Valera again and the game ends. You are asked to calculate the maximum total number of soldiers that may be killed during the game.

    Input
    The input data consist of a single integer n ( 2 ≤ n ≤ 10 8 , n is even). Please note that before the game starts there are 2 n soldiers on the fields.

    Output
    Print a single number — a maximum total number of soldiers that could be killed in the course of the game in three turns. Examples

    Input
    2

    Output
    3

    Input
    4

    Output
    6

    Note
    The first sample test: 1) Valera's soldiers 1 and 2 shoot at Arcady's soldier 1. 2) Arcady's soldier 2 shoots at Valera's soldier 1. 3) Valera's soldier 1 shoots at Arcady's soldier 2. There are 3 soldiers killed in total: Valera's soldier 1 and Arcady's soldiers 1 and 2.
*/

/*@ predicate IsValidSolution(long long int n, integer result) =
    \exists integer turn_v1, turn_a1, turn_v2;
    turn_v1 + turn_v2 <= n && // At most n soldiers of Arcady can be killed
    turn_v1 >= 1 && turn_v2 >= 1 && // The number of killed soldiers per round is non-negative
    n - turn_v1 >= turn_a1 >= 1 && // At most (n - killed) soldiers of Valera can be killed
    turn_v2 <= n  - turn_a1 && // At most (n - our killed soldiers) of Arcady can be killed
    turn_v2 <= n  - turn_v1 && // At most (n - their killed  soldiers) of Arcady can be killed
    result == turn_v1 + turn_a1 + turn_v2 && // The number of killed soldiers over the three rounds
    turn_v1 + turn_a1 + turn_v2 <= 2 * n;  // Ensure that at most 2 * n soldiers are killed
*/

/*@ predicate existsLargerSolution(long long int n, integer result) =
    \exists long long int x;
    x > result && IsValidSolution(n, x);
*/

/*@
    requires 2 <= n <= 100000000;
    requires n % 2 == 0;
    requires \valid(out);
    assigns *out;
    ensures IsValidSolution(n, *out);
    ensures !existsLargerSolution(n, *out);
*/
void CalculateMaximumSoldiersKilled(long long int n, int *out)
{
    *out = (3 * n) / 2;
}