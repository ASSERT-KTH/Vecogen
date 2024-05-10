/*
    Today an outstanding event is going to happen in the forest — hedgehog Filya will come to his old fried Sonya! Sonya is an owl and she sleeps during the day and stay awake from minute l1 to minute r1 inclusive. Also, during the minute k she prinks and is unavailable for Filya. Filya works a lot and he plans to visit Sonya from minute l2 to minute r2 inclusive. Calculate the number of minutes they will be able to spend together.

    Input
    The only line of the input contains integers l1 , r1 , l2 , r2 and k (1 ≤ l1 , r1 , l2 , r2 , k ≤ 10^18 , l 1 ≤ r 1 , l 2 ≤ r 2 ), providing the segments of time for Sonya and Filya and the moment of time when Sonya prinks.

    Output
    Print one integer — the number of minutes Sonya and Filya will be able to spend together.
*/
void calculateSharedTime(long l1, long r1, long l2, long r2, long k, long *out);