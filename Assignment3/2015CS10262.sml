structure FOL = 
struct
    datatype Term = CONST of string
        | VAR of string
        | FUNC of string * Term list
    datatype Form = TOP1                        | BOTTOM1
        | PRED of string * Term list            | NOT1 of Form
        | AND1 of Form * Form                   |  OR1 of Form * Form
        | IMP1 of Form * Form                   | IFF1 of Form * Form
        | ITE1 of Form * Form * Form
        | FORALL of string * Form
        | EXISTS of string * Form

    (* Function to make all variable name different in the formula *)
    fun standardizeVar (x: Form) =  x

    fun makePrenex (x: Form) = 
    (
        let
            fun isQuantFree (x: Form) = case x
                of FORALL(_,_) => false
                |  EXISTS(_,_) => false
                |  TOP1 => true
                |  BOTTOM1 => true
                |  PRED(_,_) => true
                |  NOT1(x) => isQuantFree x
                |  AND1(a,b) => ((isQuantFree a) and (isQuantFree b))
                |  OR1(a,b) => ((isQuantFree a) and (isQuantFree b))
                |  IMP1(a,b) => ((isQuantFree a) and (isQuantFree b))
                |  IFF1(a,b) => ((isQuantFree a) and (isQuantFree b))
                |  ITE(a,b,c) => (((isQuantFree a) and (isQuantFree b)) and (isQuantFree c))
            let standardForm = (standardizeVar x)
        in
        case standardForm
        of PRED(a,b) => PRED(a,b)
        |  TOP1 => TOP1 
        |  BOTTOM1 => BOTTOM1
        |  FORALL(str,form) => FORALL(str,(makePrenex form))
        |  EXISTS(str,form) => EXISTS(str,(makePrenex form))
        |  NOT1(FORALL(x,f)) => EXISTS(x,NOT(f))
        |  NOT1(EXISTS(x,f)) => FORALL(x,NOT(f))
        |  NOT1(x) => if (isQuantFree x) then NOT1(x) else (makePrenex NOT1( makePrenex x))
        |  AND1(FORALL(x,f),b) => FORALL(x,makePrenex (AND1(f,b)))
        |  AND1(EXISTS(x,f),b) => EXISTS(x,makePrenex (AND1(f,b)))
        |  AND1(a,FORALL(x,f)) => FORALL(x,makePrenex (AND1(a,f)))
        |  AND1(a,EXISTS(x,f)) => EXISTS(x,makePrenex (AND1(a,f)))
        |  AND1(a,b) => (
                            let
                                a1 = (isQuantFree a)
                                a2 = (isQuantFree b)
                            in
                                if (a1 and a2) then (AND(a,b))
                                else if ((not a1) and (not a2)) then (makePrenex (AND(makePrenex a,makePrenex b)))
                                else if (not a1) then (makePrenex (AND(makePrenex a,b)))
                                else if (not a2) then (makePrenex (AND(a,makePrenex b)))
                            end
                       )
        |  OR1(FORALL(x,f),b) => FORALL(x,makePrenex (OR1(f,b)))
        |  OR1(EXISTS(x,f),b) => EXISTS(x,makePrenex (OR1(f,b)))
        |  OR1(a,FORALL(x,f)) => FORALL(x,makePrenex (OR1(a,f)))
        |  OR1(a,EXISTS(x,f)) => EXISTS(x,makePrenex (OR1(a,f)))
        |  OR1(a,b) => (
                            let
                                a1 = (isQuantFree a)
                                a2 = (isQuantFree b)
                            in
                                if (a1 and a2) then (OR1(a,b))
                                else if ((not a1) and (not a2)) then (makePrenex (OR1(makePrenex a,makePrenex b)))
                                else if (not a1) then (makePrenex (OR1(makePrenex a,b)))
                                else if (not a2) then (makePrenex (OR1(a,makePrenex b)))
                            end
                       )
        |  IMP1(a,b) => makePrenex (OR(NOT(a),b))
        |  IFF1(a,b) => makePrenex (OR(AND(a,b),AND(NOT a, NOT b)))
        |  ITE1(a,b,c) => makePrenex (OR(AND(a,b),AND(NOT a, c)))
    )

    fun makePCNF (x: Form) = x

    fun makeSCNF (x: Form) = x

    fun resolve (x: Form) = true
end