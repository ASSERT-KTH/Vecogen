/*@
// Compute the global place number for (lane,desk,side) in an n×m classroom
    logic integer place_index(integer lane, integer desk, char side,
                              integer n, integer m) =
      ((lane - 1) * m + (desk - 1)) * 2
      + (side == 'L' ? 1 : 2);
*/

/*@
requires 1 <= n <= 10000;
    requires 1 <= m <= 10000;
    requires 1 <= k <= 2 * n * m;
    assigns \nothing;
    ensures 1 <= \result.lane && \result.lane <= n;
    ensures 1 <= \result.desk  && \result.desk  <= m;
    ensures \result.side == 'L' || \result.side == 'R';
    ensures place_index(\result.lane, \result.desk, \result.side, n, m) == k;
*/

