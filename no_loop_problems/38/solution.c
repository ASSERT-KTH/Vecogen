/*
    Ari the monster always wakes up very early with the first ray of the sun and the first thing she does is feeding her squirrel. Ari draws a regular convex polygon on the floor and numbers it's vertices 1, 2, ..., n in clockwise order. Then starting from the vertex 1 she draws a ray in the direction of each other vertex. The ray stops when it reaches a vertex or intersects with another ray drawn before. Ari repeats this process for vertex 2, 3, ..., n (in this particular order). And then she puts a walnut in each region inside the polygon. Ada the squirrel wants to collect all the walnuts, but she is not allowed to step on the lines drawn by Ari. That means Ada have to perform a small jump if she wants to go from one region to another. Ada can jump from one region P to another region Q if and only if P and Q share a side or a corner . Assuming that Ada starts from outside of the picture, what is the minimum number of jumps she has to perform in order to collect all the walnuts? */

/*@
    requires \valid(out);
    requires 3 <= n <= 54321;
    assigns *out;
*/
void calculateMinimumSquirrelJumps(int n, long *out)
{
    *out = (long)(n - 2) * (n - 2);
}
