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
    fun standardizeVar (x: Form) =
    (
        let
            fun findMap (mp: (string*string) list) (var: string) = case mp
                of [] => var
                |  (v,mapping)::rest => if (v=var) then mapping else findMap rest var
            fun replTerm (tl: Term list) (mp: (string*string) list) = case tl
                of [] => []
                |  (VAR x)::t => (VAR (findMap mp x))::(replTerm t mp)
                |  (FUNC(str,l))::t => (FUNC(str,replTerm l mp))::(replTerm t mp)
                |  (CONST x)::t => (CONST x)::(replTerm t mp)
            fun recurseRepl (x:Form) (mp: (string*string) list) (pos: string) = case x
                of PRED(str,tl) => PRED(str,replTerm tl mp)
                |  FORALL(str,fm) => FORALL((pos^".1"),recurseRepl fm ((str,(pos^".1"))::mp) (pos^".1"))
                |  EXISTS(str,fm) => EXISTS((pos^".1"),recurseRepl fm ((str,(pos^".1"))::mp) (pos^".1"))
                |  TOP1 => TOP1
                |  BOTTOM1 => BOTTOM1
                |  NOT1 a => NOT1(recurseRepl a mp (pos^".1"))
                |  AND1(a,b) => AND1(recurseRepl a mp (pos^".1"),recurseRepl b mp (pos^".2"))
                |  OR1(a,b) => OR1(recurseRepl a mp (pos^".1"),recurseRepl b mp (pos^".2"))
                |  IMP1(a,b) => IMP1(recurseRepl a mp (pos^".1"),recurseRepl b mp (pos^".2"))
                |  IFF1(a,b) => IFF1(recurseRepl a mp (pos^".1"),recurseRepl b mp (pos^".2"))
                |  ITE1(a,b,c) => ITE1(recurseRepl a mp (pos^".1"),recurseRepl b mp (pos^".2"),recurseRepl c mp (pos^".3"))
        in
            recurseRepl x [] "1"
        end
    )

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
                |  AND1(a,b) => ((isQuantFree a) andalso (isQuantFree b))
                |  OR1(a,b) => ((isQuantFree a) andalso (isQuantFree b))
                |  IMP1(a,b) => ((isQuantFree a) andalso (isQuantFree b))
                |  IFF1(a,b) => ((isQuantFree a) andalso (isQuantFree b))
                |  ITE1(a,b,c) => (((isQuantFree a) andalso (isQuantFree b)) andalso (isQuantFree c))
            
            val standardForm = (standardizeVar x)
        in
        case standardForm
        of PRED(a,b) => PRED(a,b)
        |  TOP1 => TOP1 
        |  BOTTOM1 => BOTTOM1
        |  FORALL(str,form) => FORALL(str,(makePrenex form))
        |  EXISTS(str,form) => EXISTS(str,(makePrenex form))
        |  NOT1(FORALL(x,f)) => EXISTS(x,NOT1(f))
        |  NOT1(EXISTS(x,f)) => FORALL(x,NOT1(f))
        |  NOT1(x) => if (isQuantFree x) then NOT1(x) else (makePrenex (NOT1( makePrenex x)))
        |  AND1(FORALL(x,f),b) => FORALL(x,makePrenex (AND1(f,b)))
        |  AND1(EXISTS(x,f),b) => EXISTS(x,makePrenex (AND1(f,b)))
        |  AND1(a,FORALL(x,f)) => FORALL(x,makePrenex (AND1(a,f)))
        |  AND1(a,EXISTS(x,f)) => EXISTS(x,makePrenex (AND1(a,f)))
        |  AND1(a,b) => (
                            let
                                val a1 = (isQuantFree a)
                                val a2 = (isQuantFree b)
                            in
                                if (a1 andalso a2) then (AND1(a,b))
                                else if ((not a1) andalso (not a2)) then (makePrenex (AND1(makePrenex a,makePrenex b)))
                                else if (not a1) then (makePrenex (AND1(makePrenex a,b)))
                                else (makePrenex (AND1(a,makePrenex b)))
                            end
                       )
        |  OR1(FORALL(x,f),b) => FORALL(x,makePrenex (OR1(f,b)))
        |  OR1(EXISTS(x,f),b) => EXISTS(x,makePrenex (OR1(f,b)))
        |  OR1(a,FORALL(x,f)) => FORALL(x,makePrenex (OR1(a,f)))
        |  OR1(a,EXISTS(x,f)) => EXISTS(x,makePrenex (OR1(a,f)))
        |  OR1(a,b) => (
                            let
                                val a1 = (isQuantFree a)
                                val a2 = (isQuantFree b)
                            in
                                if (a1 andalso a2) then (OR1(a,b))
                                else if ((not a1) andalso (not a2)) then (makePrenex (OR1(makePrenex a,makePrenex b)))
                                else if (not a1) then (makePrenex (OR1(makePrenex a,b)))
                                else (makePrenex (OR1(a,makePrenex b)))
                            end
                       )
        |  IMP1(a,b) => makePrenex (OR1(NOT1(a),b))
        |  IFF1(a,b) => makePrenex (OR1(AND1(a,b),AND1(NOT1 a, NOT1 b)))
        |  ITE1(a,b,c) => makePrenex (OR1(AND1(a,b),AND1(NOT1 a, c)))
        end
    )

    fun makePCNF (x: Form) = x

    fun makeSCNF (x: Form) = x

    fun resolve (x: Form) = true
end