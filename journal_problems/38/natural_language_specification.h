
/*In a certain geometric context, the goal is to compute the volume of a triangular prism. 
  This volume is determined by the dimensions of the prism, which include the base of the triangle, 
  the height of the triangle, and the length of the prism itself. 

  Input
  - base: a positive integer representing the length of the base of the triangular face (greater than 0).
  - height: a positive integer representing the height of the triangular face (greater than 0).
  - length: a positive integer representing the length of the prism (greater than 0).

  Output
    - The output is an integer representing the volume of the triangular prism, calculated as 
      half the product of the base, height, and length. The resulting volume is constrained 
      to fit within the range of a standard integer.
*/


/*Multiply using a wider type to avoid intermediate signed overflow
*/

