/*The only king stands on the standard chess board. You are given his position in format column and row, where column is the column from 'a' to 'h' and row is the row from '1' to '8'. Find the number of moves permitted for the king. 

    Input
    The input contains the king's position in the format column and row (1–8). The column is given by as an integer from 1 to 8 representing 'a' to 'h', the row is given by a digit from '1' to '8'.

    Output
    Return the integer which represents the number of moves permitted for the king.
*/

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

int countKingMoves(int col, int row) {
    return (col > 1) + (col < 8) + (row > 1) + (row < 8) + 
           (col > 1 && row > 1) + (col < 8 && row > 1) + 
           (col > 1 && row < 8) + (col < 8 && row < 8);
}
