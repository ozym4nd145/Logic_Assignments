structure T = Tokens

type pos = int
type svalue = T.svalue
type ('a,'b) token = ('a,'b) T.token
type lexresult = (svalue,pos) token
type lexarg = string
type arg = lexarg

val lin = ref 1;
val col = ref 0;
val eolpos = ref 0;

val badCh : string*string*int*int -> unit = fn
        (fileName,bad,line,col) =>
        TextIO.output(TextIO.stdOut,fileName^"["
            ^Int.toString line^"."^Int.toString col
            ^"] Invalid character \""^bad^"\"\n");
val eof = fn fileName => T.P_EOF (!lin,!col);

%%

%full
%header (functor ASTLexFun(structure Tokens: AST_TOKENS));
%arg (fileName:string);
%s AST COMMENT;

alpha = [A-Za-z];
digit = [0-9];
char = {alpha}|{digit};
ws  = [\ \t];
eol = ("\013\010"|"\010"|"\013");

%%

<INITIAL>{ws}* => (lin := 1;eolpos:=0; YYBEGIN AST; continue  ());
<AST>{ws}* => (continue ());
<AST>({ws}|\.)*{eol}+ => (lin := (!lin) + 1; eolpos:=yypos+size yytext; T.P_EOL(!lin,!col));

<AST>"%" => (YYBEGIN COMMENT; T.P_EOL(!lin,!col));
<AST>"NOT" => (col:=yypos-(!eolpos); T.P_NOT(!lin,!col));
<AST>"AND" => (col:=yypos-(!eolpos); T.P_AND(!lin,!col));
<AST>"OR" => (col:=yypos-(!eolpos); T.P_OR(!lin,!col));
<AST>"IF" => (col:=yypos-(!eolpos); T.P_IF(!lin,!col));
<AST>"THEN" => (col:=yypos-(!eolpos); T.P_THEN(!lin,!col));
<AST>"IFF" => (col:=yypos-(!eolpos); T.P_IFF(!lin,!col));
<AST>"ELSE" => (col:=yypos-(!eolpos); T.P_ELSE(!lin,!col));
<AST>"TRUE" => (col:=yypos-(!eolpos); T.P_TRUE(!lin,!col));
<AST>"FALSE" => (col:=yypos-(!eolpos); T.P_FALSE(!lin,!col));
<AST>"(" => (col:=yypos-(!eolpos); T.P_LPAR(!lin,!col));
<AST>")" => (col:=yypos-(!eolpos); T.P_RPAR(!lin,!col));
<AST>{char}+ => (col:=yypos-(!eolpos); T.P_ATOM(yytext,!lin,!col));
<AST>.   => (col:=yypos-(!eolpos);
            badCh(fileName,yytext,!lin,!col);
            T.P_ILLCH(!lin,!col));

<COMMENT>{eol} => (lin:=(!lin)+1;eolpos:=yypos+size yytext;
                    YYBEGIN AST; continue());
<COMMENT>. => (continue());
