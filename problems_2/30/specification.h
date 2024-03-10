/*  A. Wizards' Duel
    Harry Potter and He-Who-Must-Not-Be-Named engaged in a fight to the death once again. This time they are located at opposite ends of the corridor of length l. Two opponents simultaneously charge a deadly spell in the enemy. We know that the impulse of Harry's magic spell flies at a speed of p meters per second, and the impulse of You-Know-Who's magic spell flies at a speed of q meters per second. The impulses are moving through the corridor toward each other, and at the time of the collision they turn round and fly back to those who cast them without changing their original speeds. Then, as soon as the impulse gets back to it's caster, the wizard reflects it and sends again towards the enemy, without changing the original speed of the impulse. Since Harry has perfectly mastered the basics of magic, he knows that after the second collision both impulses will disappear, and a powerful explosion will occur exactly in the place of their collision. However, the young wizard isn't good at math, so he asks you to calculate the distance from his position to the place of the second meeting of the spell impulses, provided that the opponents do not change positions during the whole fight. */

/*@
    requires \valid(out);
    requires 1 <= l <= 1000;
    requires 1 <= p <= 500;
    requires 1 <= q <= 500;
    assigns *out;

    // In the code specification the result and the logic variable should differ by 0.0001
    ensures \abs(((l / (p + q)) * p) - *out)/(\max(1, (l / (p + q)) * p)) <= 0.0001;
*/
void problem(int l, int p, int q, int *out);