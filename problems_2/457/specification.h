/*  Blackjack
    One rainy gloomy evening when all modules hid in the nearby cafes to drink hot energetic cocktails, the Hexadecimal virus decided to fly over the Mainframe to look for a Great Idea. And she has found one! Why not make her own Codeforces, with blackjack and other really cool stuff? Many people will surely be willing to visit this splendid shrine of high culture. In Mainframe a standard pack of 52 cards is used to play blackjack. The pack contains cards of 13 values: 2 , 3 , 4 , 5 , 6 , 7 , 8 , 9 , 10 , jacks, queens, kings and aces. Each value also exists in one of four suits: hearts, diamonds, clubs and spades. Also, each card earns some value in points assigned to it: cards with value from two to ten earn from 2 to 10 points, correspondingly. An ace can either earn 1 or 11 , whatever the player wishes. The picture cards (king, queen and jack) earn 10 points. The number of points a card earns does not depend on the suit. The rules of the game are very simple. The player gets two cards, if the sum of points of those cards equals n , then the player wins, otherwise the player loses. The player has already got the first card, it's the queen of spades. To evaluate chances for victory, you should determine how many ways there are to get the second card so that the sum of points exactly equals n .*/

/*@
    requires \valid(out);
    requires 1 <= n <= 25;
    assigns *out;
    behavior n_11_to_19_or_21:
        assumes n >= 11 && n <= 19 || n == 21;
        ensures *out == 4;
    behavior n_20:
        assumes n == 20;
        ensures *out == 15;
    behavior n_other:
        assumes n != 20 && !(n >= 11 && n <= 19 || n == 21);
        ensures *out == 0;
    complete behaviors;
    disjoint behaviors;
*/
void problem(int n, int *out);