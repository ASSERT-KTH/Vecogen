/* A. New Year and Days
    Today is Wednesday, the third day of the week. What's more interesting is that tomorrow is the last day of the year 2015. Limak is a little polar bear. He enjoyed this year a lot. Now, he is so eager to the coming year 2016. Limak wants to prove how responsible a bear he is. He is going to regularly save candies for the entire year 2016! He considers various saving plans. He can save one candy either on some fixed day of the week or on some fixed day of the month. Limak chose one particular plan. He isn't sure how many candies he will save in the 2016 with his plan. Please, calculate it and tell him.
*/

//@ logic integer \strlen(char* p);

/*@ // src and dest cannot overlap
@ requires \base_addr(src) != \base_addr(dest);
@ // src is a valid C string
@ requires \strlen(src) >= 0 ;
@ // dest is large enough to store a copy of src up to the 0
@ requires \valid(dest+(0..\strlen(src)));
@ ensures
@ \forall integer k; 0 <= k <= \strlen(src) ==> dest[k] == src[k];
@*/
strcpy(char *dest, const char *src)
{
    int i;
    for (i = 0; src[i] != '\0'; ++i)
    {
        dest[i] = src[i];
    }
    dest[i] = '\0';
}