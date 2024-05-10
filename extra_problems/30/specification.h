/*
    Harry Potter and He-Who-Must-Not-Be-Named engaged in a fight to the death once again. This time they are located at opposite ends of the corridor of length l. Two opponents simultaneously charge a deadly spell in the enemy. We know that the impulse of Harry's magic spell flies at a speed of p meters per second, and the impulse of You-Know-Who's magic spell flies at a speed of q meters per second. The impulses are moving through the corridor toward each other, and at the time of the collision they turn round and fly back to those who cast them without changing their original speeds. Then, as soon as the impulse gets back to it's caster, the wizard reflects it and sends again towards the enemy, without changing the original speed of the impulse. Since Harry has perfectly mastered the basics of magic, he knows that after the second collision both impulses will disappear, and a powerful explosion will occur exactly in the place of their collision. However, the young wizard isn't good at math, so he asks you to calculate the distance from his position to the place of the second meeting of the spell impulses, provided that the opponents do not change positions during the whole fight. */

// Predicate that checks if the solution is within the margin
/*@ predicate IsWithinMargin(integer l, integer p, integer q, real out) =
    \exists integer margin, jury_solution;
    -0.0001 <= margin <= 0.0001 &&
    jury_solution == ((l * p) / (p + q)) &&
    \abs(jury_solution - out) / \max(1, jury_solution) <= margin;
*/

/*@
    requires \valid(out);
    requires 1 <= l <= 1000;
    requires 1 <= p <= 500;
    requires 1 <= q <= 500;
    assigns *out;
    ensures IsWithinMargin(l, p, q, *out);
*/
void calculateSecondSpellCollisionDistance(double l, double p, double q, double *out);
