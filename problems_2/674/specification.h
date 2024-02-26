/*  A. HQ9+
    HQ9+ is a joke programming language which has only four one-character instructions: " H " prints " Hello, World! ", " Q " prints the source code of the program itself, " 9 " prints the lyrics of "99 Bottles of Beer" song, " + " increments the value stored in the internal accumulator. Instructions " H " and " Q " are case-sensitive and must be uppercase. The characters of the program which are not instructions are ignored. You are given a program written in HQ9+. You have to figure out whether executing this program will produce any output.*/

/*@
    predicate HasP(const char* s, integer len) =
        \exists integer i; 0 <= i < len && s[i] == 'P';
    predicate HasQ(const char* s, integer len) =
        \exists integer i; 0 <= i < len && s[i] == 'Q';
    predicate Has9(const char* s, integer len) =
        \exists integer i; 0 <= i < len && s[i] == '9';
    predicate HasPlus(const char* s, integer len) =
        \exists integer i; 0 <= i < len && s[i] == '+';

    requires \valid_read(s + (0..n-1));
    assigns \nothing;
    ensures \result == "TRUE" <==> HasH(s, n) || HasQ(s, n) || Has9(s, n) || HasPlus(s, n);
*/
int problem(char *s);
