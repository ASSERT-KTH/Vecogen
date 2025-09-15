/*The function, named 'foo', accepts an integer 'n' as input and then performs a calculation based on the value of 'n'. If 'n' is greater than 100, the function subtracts 10 from 'n' and returns the result. However, if 'n' is less than or equal to 100, the function performs a recursive operation where it adds 11 to 'n' and passes this result into another call of the 'foo' function. This recursive operation continues until 'n' becomes greater than 100. The final output is then returned.

  input
  The input to the function is a single integer 'n'. The value of 'n' must lie within the range -1000 to 1000, inclusive.

  Output
  The output of the function is a single integer. If the input 'n' is greater than 100, the output will be 'n' minus 10. If 'n' is less than or equal to 100, the output will be 91, following the recursive operations specified in the function.
*/

/*@
requires -1000 <= n <= 1000; // Add a reasonable input range
  decreases n > 100 ? 1 : 102 - n;
  assigns \nothing;
  ensures ((n <= 100) ==> (\result == 91));
  ensures ((n > 100) ==> (\result == (n-10)));
*/

int foo(int n) {
  if (n > 100) {
    return n - 10;
  } else {
    return foo(foo(n + 11));
  }
}
