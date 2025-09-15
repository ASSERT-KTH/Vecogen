/*@
// Given a column (1–8) and row (1–8), compute how many of the
    // eight possible king‐moves stay on the board.
    logic integer king_moves_pos(integer col, integer row) =
        (col > 1            ? 1 : 0)  // left
        + (col < 8            ? 1 : 0)  // right
        + (row > 1            ? 1 : 0)  // down
        + (row < 8            ? 1 : 0)  // up
        + (col > 1 && row > 1 ? 1 : 0)  // down-left
        + (col < 8 && row > 1 ? 1 : 0)  // down-right
        + (col > 1 && row < 8 ? 1 : 0)  // up-left
        + (col < 8 && row < 8 ? 1 : 0); // up-right
*/

/*@
requires 1 <= col <= 8;
    requires 1 <= row <= 8;
    assigns \nothing;
    ensures \result == king_moves_pos(col, row);
*/

