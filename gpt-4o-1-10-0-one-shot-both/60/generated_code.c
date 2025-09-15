/*There is a card game called "Durak", which means "Fool" in Russian. The game is quite popular in the countries that used to form USSR. The problem does not state all the game's rules explicitly — you can find them later yourselves if you want. To play durak you need a pack of 36 cards. Each card has a suit (" S ", " H ", " D " and " C ") and a rank (in the increasing order " 6 ", " 7 ", " 8 ", " 9 ", " T ", " J ", " Q ", " K " and " A "). At the beginning of the game one suit is arbitrarily chosen as trump. The players move like that: one player puts one or several of his cards on the table and the other one should beat each of them with his cards. A card beats another one if both cards have similar suits and the first card has a higher rank then the second one. Besides, a trump card can beat any non-trump card whatever the cards’ ranks are. In all other cases you can not beat the second card with the first one. You are given the trump suit and two different cards. Determine whether the first one beats the second one or not.

    Input
    The first input contains the tramp suit. It is " S ", " H ", " D " or " C ". The second and third input contains the description of the two different cards. Each card is described by one word consisting of two symbols. The first symbol stands for the rank (" 6 ", " 7 ", " 8 ", " 9 ", " T ", " J ", " Q ", " K " and " A "), and the second one stands for the suit (" S ", " H ", " D " and " C ").

    Output
    Return 1 if the first cards beats the second one. Otherwise, return 0.
*/

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

int beats_card(char trump, char card1[2], char card2[2]) {
    int rank1 = (card1[0] == '6') ? 0 :
                (card1[0] == '7') ? 1 :
                (card1[0] == '8') ? 2 :
                (card1[0] == '9') ? 3 :
                (card1[0] == 'T') ? 4 :
                (card1[0] == 'J') ? 5 :
                (card1[0] == 'Q') ? 6 :
                (card1[0] == 'K') ? 7 :
                (card1[0] == 'A') ? 8 : -1;

    int rank2 = (card2[0] == '6') ? 0 :
                (card2[0] == '7') ? 1 :
                (card2[0] == '8') ? 2 :
                (card2[0] == '9') ? 3 :
                (card2[0] == 'T') ? 4 :
                (card2[0] == 'J') ? 5 :
                (card2[0] == 'Q') ? 6 :
                (card2[0] == 'K') ? 7 :
                (card2[0] == 'A') ? 8 : -1;

    if (card1[1] == card2[1]) {
        return rank1 > rank2;
    } else if (card1[1] == trump) {
        return 1;
    } else {
        return 0;
    }
}
