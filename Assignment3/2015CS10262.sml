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
    exception NOT_UNIFIABLE
    exception NO_CLAUSE_TO_UNIFY

    type substitution = ((Term*Term) list)
    type clause = Form list

    (* Function to check if a Form is quantifier free *)
    fun isQuantFree (x: Form) =
    (
        case x
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
    )

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

    fun makeSCNF (x: Form) =
    (
        let
            fun findMap (mp: (Term*Term) list) (var: Term) = case mp
                of [] => var
                |  (v,mapping)::rest => if (v=var) then mapping else findMap rest var
            fun applyMapTermList (mp: (Term*Term) list) (tl:Term list) = case tl
                of [] => []
                |  (CONST a)::r => (CONST a)::(applyMapTermList mp r)
                |  (VAR a)::r => (findMap mp (VAR a))::(applyMapTermList mp r)
                |  (FUNC (str,e))::r => (FUNC(str,applyMapTermList mp e))::(applyMapTermList mp r)
            fun applyMap (mp: (Term*Term) list) (f: Form) = case f
                of TOP1 => TOP1
                |  BOTTOM1 => BOTTOM1
                |  PRED(str,tl) => PRED(str,applyMapTermList mp tl)
                |  AND1(a,b) => AND1(applyMap mp a,applyMap mp b)
                |  OR1(a,b) => OR1(applyMap mp a,applyMap mp b)
                |  NOT1(a) => NOT1(applyMap mp a)
                |  _       => raise Error("Input Proposition is not of base form")

            fun makeSkolEntry (str: string) (pre: string) (idx: int) (tl: Term list) = 
                let
                    val name = (pre^(Int.toString idx))
                    val entryFun = (VAR str,FUNC(name,tl))
                    val entryCons = (VAR str,CONST(name))
                in
                    if (tl=[]) then entryCons else entryFun
                end

            fun skolemize (x: Form) (mp: (Term*Term) list) (pre: string) (idx: int) (tl: Term list) = case x
                of FORALL(str,f) => FORALL(str,skolemize f mp pre idx ((VAR str)::tl))
                | EXISTS(str,f) => skolemize f ((makeSkolEntry str pre idx tl)::mp) pre (idx+1) (tl)
                | f => applyMap mp f
        in
            skolemize x [] "__SKOVAR_" 0 []
        end
    )

    fun occurs (VAR(a): Term) (t: Term) = case t
        of CONST(_) => false
        |  VAR(b) => (a=b)
        |  FUNC(str,tl) => occursinlist (VAR a) tl
    and occursinlist (VAR(a): Term) (tl: Term list) = case tl
        of [] => false
        |  t::ts => (occurs (VAR a) t) orelse (occursinlist (VAR a) ts)
    
    fun applySubst ((key,value): Term*Term) (t: Term) = case t
        of CONST(_) => t
        |  VAR(_) => if t=key then value else t
        |  FUNC(str,tl) => FUNC(str,applySubstList (key,value) tl)
    and applySubstList (sub: Term*Term) (list: Term list) = case list
        of [] => []
        |  t1::tl => (applySubst sub t1)::(applySubstList sub tl)
    
    fun unify (l1: Term list) (l2: Term list) (sub: substitution): substitution =
    (
        case (l1,l2)
        of ([],[]) => sub
        |  (t1::tl1,t2::tl2) => if t1 = t2 then unify tl1 tl2 sub else
                                (
                                    case (t1,t2)
                                        of (CONST a,CONST b) => if a=b then sub else raise NOT_UNIFIABLE
                                        |  (FUNC(a,al),FUNC(b,bl)) => if a=b then unify (al@tl1) (bl@tl2) sub
                                                                    else raise NOT_UNIFIABLE
                                        |  (VAR(a),_) => if (occurs (VAR a) t2) then raise NOT_UNIFIABLE
                                                        else
                                                            let
                                                                val new_subst = (VAR(a),t2)
                                                                val new_l1 = applySubstList new_subst tl1
                                                                val new_l2 = applySubstList new_subst tl2
                                                                val new_sub = new_subst::(List.map (fn (a:Term,b) => (a,applySubst new_subst b)) sub)
                                                            in
                                                                unify new_l1 new_l2 new_sub
                                                            end
                                        |   (_,VAR(a)) => unify l2 l1 sub
                                        |   (_,_) => raise NOT_UNIFIABLE
                                )
        | _ => raise NOT_UNIFIABLE
    )

    fun containsTop (x: Form list) = case x
        of [] => false
        |  a::tl => if a=TOP1 then true else containsTop tl
    fun makeSet (x: Form) =
    (
        let
            fun expandOr (x: Form) = case x
                of OR1(a,b) => (expandOr a) @ (expandOr b)
                | BOTTOM1 => []
                | _ => [x]
            fun expandAnd (x: Form) = case x
                of AND1(a,b) => (expandAnd a)@(expandAnd b)
                |  _    => let val cl = expandOr x in if (containsTop cl) then [] else [cl] end
            fun skipFor (x: Form) = case x
                of FORALL(_,f) => skipFor f
                |  _ => expandAnd x
        in
            skipFor x
        end
    )

    fun posPred (cl: clause) = case cl
        of [] => []
        |  PRED(a,b)::tl => PRED(a,b)::(posPred tl)
        |  NOT1(PRED(a,b))::tl => posPred tl
        |  _ => raise Error("Or clauses are not pure")

    fun negPred (cl: clause) = case cl
        of [] => []
        |  (NOT1(PRED(a,b)))::tl => PRED(a,b)::(negPred tl)
        |  PRED(a,b)::tl => negPred tl
        |  _ => raise Error("Or clauses are not pure")
    
    fun exists (a: 'a) (b: 'a list) = case b
        of [] => false
        |  (x::tl) => if x=a then true else exists a tl

    fun existsPred (a:string) (b: Clause) = case b
        of [] => false
        |  (PRED(c,d))::tl => if c=a then true else existsPred a tl
        |  _::tl => existsPred a tl

    fun existsNotPred (a:string) (b: Clause) = case b
        of [] => false
        |  (NOT1(PRED(c,d)))::tl => if c=a then true else existsNotPred a tl
        |  _::tl => existsNotPred a tl
    
    fun commonPred (a: clause) (b: clause) = case a
        of [] => NONE
        |  PRED(p,q)::tl => if (existsPred p b) then SOME(p) else commonPred tl b
        |  _ => raise Error("All clauses are not pred in common Pred")

    fun isContradCl (cl: clause) =
        let
            val pos = posPred cl
            val neg = negPred cl
        in
            case (commonPred pos neg)
                of SOME _ => true
                |  NONE => false
        end
    fun simplify (set: clause list) = case set
        of [] => []
        |  cl::cl_list => if isContradCl cl then (simplify cl_list) else cl::(simplify cl_list)
    
    fun getAllPos (set: clause list) = case set
        of [] => []
        |  cl::cl_list => (posPred cl)::(getAllPos cl_list)
    fun getAllNeg (set: clause list) = case set
        of [] => []
        |  cl::cl_list => (negPred cl)::(getAllNeg cl_list)

    fun selectResolvePred (set: clause list) =
    (
        let
            val allpos = getAllPos set
            val allneg = getAllNeg set
        in
            commonPred allpos allneg
        end
    )

    fun selectPred (pred: string) (set: clause list) (newset: clause list) = case set
        of [] => raise Error("Selected predicate does not exist")
        |  a::tl => if (existsPred pred a) then (a,tl@newset) else selectPred pred tl (a::newset)
    fun selectNotPred (pred: string) (set: clause list) (newset: clause list) = case set
        of [] => raise Error("Selected predicate does not exist")
        |  a::tl => if (existsNotPred pred a) then (a,tl@newset) else selectNotPred pred tl (a::newset)

    fun separateClause (pred: string) (cl:clause) (restCl: clause list) (unift: Term list) = case cl
        of [] => (restCl,unift)
        |  (PRED(a,b))::tl => if a=pred then separateClause pred tl restCl (unift@b)
                              else separateClause pred tl (PRED(a,b)::restCl) unift
        |  (NOT1(PRED(a,b)))::tl => if a=pred then separateClause pred tl restCl (unift@b)
                              else separateClause pred tl (NOT1(PRED(a,b))::restCl) unift
        |   _ => raise Error("The terms in clause are not in pure form")
    
    fun unifyTermList (terms: Term list)=
    (
        let
            fun copy (t: Term) (terms: Term list) = case terms
                of [] => []
                |  a::b => t::(copy t b)
        in
            case terms
                of [] => []
                |  [a] => []
                |  a::tl => let sec = copy a tl in unify sec tl [] end
        end
    )

    fun substTermList (subs:substitution) (b: Term list) = case subs
        of [] => b
        |  s::tl => substTermList tl (applySubstList s b)
    fun substClause (subs: substitution) (cl: clause) = case cl
        of [] => []
        |  PRED(a,b)::tl => PRED(a,substTermList subs b)::(substClause subs tl)
        |  NOT1(PRED(a,b))::tl => NOT1(PRED(a,substTermList subs b))::(substClause subs tl)
        |   _ => raise Error("The terms in clause are not in pure form")

    fun resolveStep (set: clause list) =
    (
        let
          fun selectBaseClause (set: clause list) (rest_set: clause list)= case set
            of [] => raise NO_CLAUSE_TO_UNIFY
            |  cl::tl => selectBaseProp cl (rest_set@tl) handle NO_CLAUSE_TO_UNIFY => selectBaseClause tl (cl::rest_set)
          fun selectBaseProp (cl: clause) (rem_set: clause list) = case cl
            of [] => raise NO_CLAUSE_TO_UNIFY
            |  (PROP(a,b))::tl => selectNotPropClause a cl rem_set [] handle NO_CLAUSE_TO_UNIFY => selectBaseProp tl rem_set
            |  (NOT1(PROP(a,b)))::tl => selectPropClause a cl rem_set [] handle NO_CLAUSE_TO_UNIFY => selectBaseProp tl rem_set
          fun selectNotPropClause (prop: string) (cl: clause) (set: clause list) (rem_set: clause list) = case set
            of [] => raise NO_CLAUSE_TO_UNIFY
            |  cl2::tl => if (existsNotPred prop cl2) then
                           ( tryUnify prop cl cl2 (tl@rem_set) handle NO_CLAUSE_TO_UNIFY => selectNotPropClause prop cl tl (cl2::rem_set))
                          else selectNotPropClause prop cl tl (cl2::rem_set)
          fun selectPropClause (prop: string) (cl: clause) (set: clause list) (rem_set: clause list) = case set
            of [] => raise NO_CLAUSE_TO_UNIFY
            |  cl2::tl => if (existsPred prop cl2) then
                           ( tryUnify prop cl cl2 (tl@rem_set) handle NO_CLAUSE_TO_UNIFY => selectPropClause prop cl tl (cl2::rem_set))
                          else selectNotPropClause prop cl tl (cl2::rem_set)
          fun tryUnify (prop: string) (cl1: clause) (cl2: clause) (set: clause list) = 
          (
            let
                val mixedClause = cl1@cl2
                val (restClause,unifyTerms) = separateClause pred mixedClause [] []
                val subs = unifyTermList unifyTerms [] handle NOT_UNIFIABLE => raise NO_CLAUSE_TO_UNIFY
                val new_clause = substClause subs restClause
            in
                new_clause::set
            end
          )
        in
          selectBaseClause set []
        end

    )


    fun reduce (set: clause list) =
    (
        let
            val simple = simplify set
        in
            if (exists [] simple) then false
            else if (simple=[]) then true
            else
            reduce(resolveStep(simple)) handle NO_CLAUSE_TO_UNIFY => true
        end
    )

    fun resolve (x: Form) =
    (
        let
            val prenex = makePrenex x
            val pcnf = makePCNF prenex
            val scnf = makeSCNF pcnf
            val set = makeSet scnf
        in
            reduce set
        end
    )
end