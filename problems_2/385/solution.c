/* Tram time limit per test 1 second memory limit per test 256 megabytes input standard input output standard output The tram in Berland goes along a straight line from the point 0 to the point s and back, passing 1 meter per t 1 seconds in both directions. It means that the tram is always in the state of uniform rectilinear motion, instantly turning around at points x = 0 and x = s . Igor is at the point x 1 . He should reach the point x 2 . Igor passes 1 meter per t 2 seconds. Your task is to determine the minimum time Igor needs to get from the point x 1 to the point x 2 , if it is known where the tram is and in what direction it goes at the moment Igor comes to the point x 1 . Igor can enter the tram unlimited number of times at any moment when his and the tram's positions coincide. It is not obligatory that points in which Igor enter and exit the tram are integers. Assume that any boarding and unboarding happens instantly. Igor can move arbitrary along the line (but not faster than 1 meter per t 2 seconds). He can also stand at some point for some time.*/

/*@
    requires \valid(out);

    assigns *out;
    ensures *out == 0 || *out == 1;
*/