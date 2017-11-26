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

    exception Error of string

    (* Function to check if a Form is quantifier free *)
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

    fun makePCNF (x: Form) =
    (
        let
            fun applyQuantFree (fnc: Form->Form) (x:Form) = case x
                of FORALL(str,f) => FORALL(str,applyQuantFree (fnc) f)
                |  EXISTS(str,f) => EXISTS(str,applyQuantFree (fnc) f)
                |  f           => if (isQuantFree f) then (fnc f) else raise Error("The given form is not Prenex")
            fun makennf (x: Form) = case x
                of TOP1 => TOP1
                |  BOTTOM1 => BOTTOM1
                |  PRED(a,b) => PRED(a,b)
                |  NOT1(TOP1) => BOTTOM1
                |  NOT1(BOTTOM1) => TOP1
                |  NOT1(NOT1(a)) => makennf a
                |  NOT1(PRED(a,b)) => NOT1(PRED(a,b))
                |  NOT1(OR1(a,b)) => AND1(makennf (NOT1 a),makennf (NOT1 b))
                |  NOT1(AND1(a,b)) => OR1(makennf (NOT1 a),makennf (NOT1 b))
                |  AND1(a,b) => AND1(makennf a,makennf b)
                |  OR1(a,b) => OR1(makennf a,makennf b)
                |  _       => raise Error("Input Proposition is not of base form")
            fun isAndFree (x:Form) = case x
                of AND1(_,_) => false
                |  OR1(a,b) => ((isAndFree a)andalso(isAndFree b))
                |  NOT1(a) => isAndFree a
                |  PRED(_,_) => true
                |  TOP1 => true
                |  BOTTOM1 => true
                |  _       => raise Error("Input Proposition is not of base form")
            fun distOr (x:Form) = case x
                of AND1(a,b) => AND1(distOr a,distOr b)
                |  NOT1(PRED(a,b)) => NOT1(PRED(a,b))
                |  TOP1 => TOP1
                |  BOTTOM1 => BOTTOM1
                |  PRED(a,b) => PRED(a,b)
                |  OR1(AND1(a,b),c) => distOr (AND1((OR1(a,c)),(OR1(b,c))))
                |  OR1(a,AND1(b,c)) => distOr (AND1((OR1(a,c)),(OR1(b,c))))
                |  OR1(a,b) =>  let
                                    val r1 = isAndFree a
                                    val r2 = isAndFree b
                                in
                                    if (r1 andalso r2) then OR1(a,b)
                                    else if ((not r1) andalso (not r2)) then (distOr (OR1(distOr a, distOr b)))
                                    else if (not r1) then (distOr (OR1 (distOr a,b)))
                                    else (distOr (OR1 (a,distOr b)))
                                end
                |  _       => raise Error("Input Proposition is not of base form")
        in
            applyQuantFree (fn x => distOr(makennf x)) x
        end
    )

    fun makeSCNF (x: Form) = x

    fun resolve (x: Form) = true
end