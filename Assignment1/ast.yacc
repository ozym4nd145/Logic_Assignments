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
    | P_EOL

%nonterm propListR of string Prop list
        | propR of string Prop 
        | iffR of string Prop
        | iftR of string Prop
        | orR of string Prop
        | andR of string Prop
        | negR of string Prop
        | basicR of string Prop
        | wordR of string

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

propListR: propR P_EOL propListR              (propR::propListR)
    | propR                                 ([propR])

propR: P_IF propR P_THEN propR P_ELSE propR (print("matching: ITE\n"); ITE(propR1,propR2,propR3))
    | iffR                                  (iffR)

iffR: iftR P_IFF iffR                       (print("matching: IFF\n"); IFF(iftR,iffR))
    | iftR                                  (iftR)

iftR: P_IF orR P_THEN iftR                  (print("matching: IMP\n"); IMP(orR,iftR))
    | orR                                   (orR)

orR: orR P_OR andR                          (print("matching: OR\n"); OR(orR,andR))
    | andR                                  (andR)

andR: andR P_AND negR                       (print("matching: AND\n"); AND(andR,negR))
    | negR                                  (negR)

negR: P_NOT negR                            (print("matching: NOT\n"); NOT(negR))
    | basicR                                (basicR)

basicR: P_TRUE                              (print("matching: TOP\n"); TOP)
    | P_FALSE                               (print("matching: BOTTOM\n"); BOTTOM)
    | P_LPAR propR P_RPAR                   (print("matching: propR\n"); propR)
    | wordR                                 (print("matching: ATOM\n"); ATOM(wordR))

wordR: P_ATOM wordR                         (print("matching: wordR: "^P_ATOM^"\n"); (P_ATOM)^" "^(wordR))
    | P_ATOM                                (print("matching: single: "^P_ATOM^"\n"); P_ATOM)