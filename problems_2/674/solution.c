/*  A. HQ9+
    HQ9+ is a joke programming language which has only four one-character instructions: " H " prints " Hello, World! ", " Q " prints the source code of the program itself, " 9 " prints the lyrics of "99 Bottles of Beer" song, " + " increments the value stored in the internal accumulator. Instructions " H " and " Q " are case-sensitive and must be uppercase. The characters of the program which are not instructions are ignored. You are given a program written in HQ9+. You have to figure out whether executing this program will produce any output.*/

/*@
  // Does the string s contain the specified character?
  predicate Has_Char(char* s, char c) =
    \exists integer i; 0 <= i < \strlen(s) && s[i] == c;

  requires \strlen(s) >= 0 ;
  assigns \nothing;
  ensures Has_Char(s, 'H') || Has_Char(s, "Q") || Has_Char(s, "Q") || Has_Char(s, "+")==> \result == "YES";
  ensures !Has_Char(s, 'H') && !Has_Char(s, "Q") && !Has_Char(s, "Q") && !Has_Char(s, "+") ==> \result == "NO";
*/

char *problem(const char *s)
{
    char p[101];
    gets(p);
    if (strstr(p, "H") || strstr(p, "Q") || strstr(p, "9") || strstr(p, "H"))
        return "YES";
    else
        return "NO";
    return 0;
}
