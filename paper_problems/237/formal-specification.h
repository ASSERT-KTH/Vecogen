/*@ predicate isValidSolution(integer N, integer out) =
    \exists integer zombies_vote_yes, zombies_vote_no;
    0 <= zombies_vote_yes <= N &&
    0 <= zombies_vote_no <= N &&
    zombies_vote_yes + zombies_vote_no + 1 == N &&
    zombies_vote_yes + 1 >= ((real) N) / 2 &&
    zombies_vote_yes + 1 == out;
*/

/*@ predicate existsSmallerSolution(integer N, integer out) =
    \exists integer zombies_vote_yes, zombies_vote_no;
    0 <= zombies_vote_yes <= N &&
    0 <= zombies_vote_no <= N &&
    zombies_vote_yes + zombies_vote_no + 1 == N &&
    zombies_vote_yes + 1 >= ((real) N) / 2 &&
    zombies_vote_yes + 1 < out;
*/

/*@
    requires \valid(out);
    requires 1 <= N <= 1000000000;
    assigns *out;
    ensures isValidSolution(N, *out);
    ensures !existsSmallerSolution(N, *out);
*/