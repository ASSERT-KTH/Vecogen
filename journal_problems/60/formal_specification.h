/*@
logic integer rank_value(char r) =
        (r == '6') ? 0 :
        (r == '7') ? 1 :
        (r == '8') ? 2 :
        (r == '9') ? 3 :
        (r == 'T') ? 4 :
        (r == 'J') ? 5 :
        (r == 'Q') ? 6 :
        (r == 'K') ? 7 :
        (r == 'A') ? 8 : -1;

    logic char rank(char* card) = card[0];
    logic char suit(char* card) = card[1];

    predicate beats(char trump, char* card1, char* card2) =
        (suit(card1) == suit(card2) &&
         rank_value(rank(card1)) > rank_value(rank(card2)))
      || (suit(card1) == trump && suit(card2) != trump);
*/

/*@
requires \valid_read(card1 + (0 .. 1));
    requires \valid_read(card2 + (0 .. 1));
    requires trump == 'S' || trump == 'H' || trump == 'D' || trump == 'C';
    requires card1[0] == '6' || card1[0] == '7' || card1[0] == '8' || card1[0] == '9' ||
             card1[0] == 'T' || card1[0] == 'J' || card1[0] == 'Q' || card1[0] == 'K' || card1[0] == 'A';
    requires card2[0] == '6' || card2[0] == '7' || card2[0] == '8' || card2[0] == '9' ||
             card2[0] == 'T' || card2[0] == 'J' || card2[0] == 'Q' || card2[0] == 'K' || card2[0] == 'A';
    requires card1[1] == 'S' || card1[1] == 'H' || card1[1] == 'D' || card1[1] == 'C';
    requires card2[1] == 'S' || card2[1] == 'H' || card2[1] == 'D' || card2[1] == 'C';
    assigns \nothing;
    ensures (\result == 1) <==> beats(trump, card1, card2);
*/

