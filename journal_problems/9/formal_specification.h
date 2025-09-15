/*@
requires -1000 <= n <= 1000; // Add a reasonable input range
  decreases n > 100 ? 1 : 102 - n;
  assigns \nothing;
  ensures ((n <= 100) ==> (\result == 91));
  ensures ((n > 100) ==> (\result == (n-10)));
*/

