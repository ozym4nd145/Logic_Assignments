open AST_TYPES
%%
%name AST
%term P_NOT
    | P_AND
    | P_OR
    | P_IF
    | P_THEN
    | P_IFF
    | P_ELSE
    | P_TRUE
    | P_FALSE
    | P_RPAR
    | P_LPAR
    | P_ATOM of string
    | P_ILLCH
    | P_EOF

%nonterm prop of string Prop | word of string

%pos int
%eop P_EOF
%noshift P_EOF
%nodefault
%verbose
%arg (fileName) :string

%nonassoc P_EOF P_LPAR P_RPAR
%right P_IFF
%right P_IF P_THEN P_ELSE
%left P_OR
%left P_AND

%%
prop:
      P_TRUE                            (TOP)
    | P_FALSE                           (BOTTOM)
    | P_LPAR prop P_RPAR                (prop)
    | P_NOT prop                        (NOT(prop))
    | prop P_AND prop                   (AND(prop1,prop2))
    | prop P_OR prop                    (OR(prop1,prop2))
    | P_IF prop P_THEN prop P_ELSE prop (ITE(prop1,prop2,prop3))
    | P_IF prop P_THEN prop             (IMP(prop1,prop2))
    | prop P_IFF prop                   (IFF(prop1,prop2))
    | word                              (ATOM(word))

word: P_ATOM word                       ((P_ATOM)^" "^(word))
    | P_ATOM                            (P_ATOM)