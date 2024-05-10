/*
    Katya studies in a fifth grade. Recently her class studied right triangles and the Pythagorean theorem. It appeared, that there are triples of positive integers such that you can construct a right triangle with segments of lengths corresponding to triple. Such triples are called Pythagorean triples . For example, triples (3, 4, 5) , (5, 12, 13) and (6, 8, 10) are Pythagorean triples. Here Katya wondered if she can specify the length of some side of right triangle and find any Pythagorean triple corresponding to such length?

    Note
    that the side which length is specified can be a cathetus as well as hypotenuse. Katya had no problems with completing this task. Will you do the same?

    Input
    The input contains single integer n (1 ≤ n ≤ 10^9 ) — the length of some side of a right triangle.

    Output
    Output two integers m and k ( 1 ≤ m , k ≤ 10 18 ), such that n , m and k form a Pythagorean triple, in the only line. In case if there is no any Pythagorean triple containing integer n , print - 1 in the only line. If there are many answers, print any of them.
*/
void findPythagoreanTripleForSide(int N, long *out1, long *out2);