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
        | iteR of string Prop
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

%%

propListR: propR P_EOL propListR            (propR::propListR)
    | propR                                 ([propR])

propR: P_IF propR P_THEN propR              ((*print("matching: IMP\n");*) IMP(propR1,propR2))
    | iffR                                  (iffR)

iffR: iteR P_IFF propR                      ((*print("matching: IFF\n");*) IFF(iteR,propR))
    | iteR                                  (iteR)

iteR: P_IF propR P_THEN iffR P_ELSE propR   ((*print("matching: ITE\n");*) ITE(propR1,iffR,propR2))
    | orR                                   (orR)

orR: orR P_OR andR                          ((*print("matching: OR\n");*) OR(orR,andR))
    | andR                                  (andR)

andR: andR P_AND negR                       ((*print("matching: AND\n");*) AND(andR,negR))
    | negR                                  (negR)

negR: P_NOT negR                            ((*print("matching: NOT\n");*) NOT(negR))
    | basicR                                (basicR)

basicR: P_TRUE                              ((*print("matching: TOP\n");*) TOP)
    | P_FALSE                               ((*print("matching: BOTTOM\n");*) BOTTOM)
    | P_LPAR propR P_RPAR                   ((*print("matching: propR\n");*) propR)
    | wordR                                 ((*print("matching: ATOM\n");*) ATOM(wordR))

wordR: P_ATOM wordR                         ((*print("matching: wordR: "^P_ATOM^"\n");*) (P_ATOM)^" "^(wordR))
    | P_ATOM                                ((*print("matching: single: "^P_ATOM^"\n");*) P_ATOM)