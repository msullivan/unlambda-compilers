structure Tokens = Tokens
structure T = Tokens
              
type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue,pos) token

val pos = ref 0
fun eof () = Tokens.EOF(!pos,!pos)

%%

%header (functor LambdaLexFun(structure Tokens : Lambda_TOKENS));

lower = [a-z];
upper = [A-Z];
digit=[0-9];
alpha = [a-zA-Z];
alnum = [a-zA-Z0-9];
ws = [\ \t];

%%

{ws}+    => (lex());

"^"      => (T.LAMBDA(yypos, yypos));
"("      => (T.LPAREN(yypos,yypos));
")"      => (T.RPAREN(yypos,yypos));
"\."     => (T.DOT(yypos,yypos));
{alnum}  => (T.NAME(yytext,yypos,yypos));

