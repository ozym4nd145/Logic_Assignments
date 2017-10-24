signature AST_SIG =
sig
  datatype ''a Prop = TOP
                    | BOTTOM
                    | ATOM of ''a
                    | NOT of ''a Prop
                    | AND of ''a Prop * ''a Prop
                    | OR of ''a Prop * ''a Prop
                    | IMP of ''a Prop * ''a Prop
                    | IFF of ''a Prop * ''a Prop
                    | ITE of ''a Prop * ''a Prop * ''a Prop

  val toPrefix: (''a -> string) -> ''a Prop -> string
  val toPostfix: (''a -> string) -> ''a Prop -> string
  val isEqual: ''a Prop -> ''a Prop -> bool

  datatype Lit =  P of string
                | N of string
  datatype Clause = CLS of (Lit list)
  datatype Cnf    = CNF of (Clause list)
  val makeCnf: string Prop list -> Cnf
  val resolve: Cnf -> bool
end

structure AST_TYPES:> AST_SIG = struct
  datatype ''a Prop = TOP
                    | BOTTOM
                    | ATOM of ''a
                    | NOT of ''a Prop
                    | AND of ''a Prop * ''a Prop
                    | OR of ''a Prop * ''a Prop
                    | IMP of ''a Prop * ''a Prop
                    | IFF of ''a Prop * ''a Prop
                    | ITE of ''a Prop * ''a Prop * ''a Prop

  datatype Lit =  P of string
                | N of string
  datatype Clause = CLS of (Lit list)
  datatype Cnf    = CNF of (Clause list)

  exception Error of string

  val makeCnf: string Prop list -> Cnf
  val resolve: Cnf -> bool

  fun baseProp (x: 'a Prop) = 
  (case x
    of IMP(a,b) => OR(NOT(baseProp a),(baseProp b))
    | IFF(a,b) => let val left = baseProp a
                      val right = baseProp b
                  in OR(AND(NOT(left),NOT(right)),AND(left,right))
                  end
    | ITE(a,b,c) => let val left = baseProp b
                        val right = baseProp c
                        val cond = baseProp a
                    in OR(AND(cond,left),AND(NOT(cond),right))
                    end
    | TOP => TOP
    | BOTTOM => BOTTOM
    | ATOM(a) => ATOM(a)
    | NOT(a)  => NOT(baseProp a)
    | AND(a,b) => AND(baseProp a,baseProp b)
    | OR(a,b) => OR(baseProp a,baseProp b)
  )

  fun nnf (x: 'a Prop) =
  (case (baseProp x)
    of TOP => TOP
    | BOTTOM => BOTTOM
    | ATOM(a) => ATOM(a)
    | NOT(TOP) => BOTTOM
    | NOT(BOTTOM) => TOP
    | NOT(ATOM a) => NOT(ATOM a)
    | NOT(NOT(a)) => nnf a
    | NOT(AND(a,b)) => OR(nnf (NOT a), nnf(NOT b))
    | NOT(OR(a,b)) => AND(nnf (NOT a), nnf(NOT b))
    | AND(a,b) => AND(nnf a, nnf b)
    | OR(a,b) => OR(nnf a,nnf b)
    | _       => raise Error("Input Proposition is not of base form")
  )

  fun pushOr (x: 'a Prop) = 
  (case (nnf x)
    of TOP => TOP
    | BOTTOM => BOTTOM
    | ATOM(a) => ATOM(a)
    | NOT(ATOM(a)) => NOT(ATOM(a))
    | AND(a,b) => AND(pushOr a,pushOr b)
    | OR(AND(a,b),c) => AND(pushOr(OR(a,c)),pushOr(OR(b,c)))
    | OR(c,AND(a,b)) => pushOr (OR(AND(a,b),c))
    | OR(a,b) => OR(pushOr a,pushOr b)
    | _       => raise Error("Input Proposition is not of nnf form")
  )

  fun flattenOr (x: string Prop) = 
    let
      exception True
      fun conv(x) = (case x
        of TOP => raise True
        |  BOTTOM => []
        |  ATOM(a) => [P(a)]
        |  NOT(ATOM(a)) => [N(a)]
        |  OR(a,TOP) => conv(a)
        |  OR(TOP,a) => conv(OR(a,TOP))
        |  OR(a,b) => conv(a)@conv(b)
        |  _     => raise Error("Only OR expression not given")
      )
    in (SOME (CLS(conv x)))
       handle True => NONE
    end

  fun flattenAnd (x: string Prop) = 
  let
    exception False
    fun conv(x) = (case x
      of AND(a,b) => conv(a)@conv(b)
      | a => (case (flattenOr a)
                of NONE => []
                | SOME (CLS []) => raise False
                | SOME a => [a]
             )
    )
  in CNF(conv x) handle False => CNF([(CLS [])])
  end

  fun cnf (x: string Prop) = flattenAnd (pushOr x)
  fun makeCnf x = foldl (fn (y, CNF l) => let val CNF(t) = cnf(y) in CNF(l@t) end) (CNF []) x


  fun existEmpty (CNF(x): Cnf): bool = let fun search (x: Clause list) = (case x
                                         of [] => false
                                         | (CLS [])::tl => true
                                         | _::tl => search tl 
                                       ) in search x end

  fun positives [] = []
  |   positives ((P a)::tl) = (P a)::(positives tl)
  |   positives ((N a)::tl) = (positives tl)

  fun negatives [] = []
  |   negatives ((N a)::tl) = (N a)::(negatives tl)
  |   negatives ((P a)::tl) = (negatives tl)

  fun removeElem ([]) a = []
  |   removeElem (b::tl) a = if(a=b) then removeElem tl a else b::(removeElem tl a)

  fun remDupl lst = let
                      fun remove acc [] = acc
                      |   remove acc (hd::tl) = remove (hd::acc) (removeElem tl hd)
                    in
                      remove [] lst
                    end

  fun isPresent x [] = false
  |   isPresent x (y::tl) = (x=y) orelse isPresent x tl

  fun findCommon (A,[]) = NONE
  |   findCommon ([],A) = NONE
  |   findCommon (L as (P l)::LL,R as (N r)::RR) = if (isPresent (N l) R) then SOME l
                                                   else if(isPresent (P r) L) then SOME r
                                                   else findCommon(LL,RR)
  |   findCommon (_,_) = raise Error("Arguments are incorrectly given!")


  fun simplifyClause (CLS(x): Clause): Clause option = let
                                        val posLst = remDupl(positives x)
                                        val negLst = remDupl(negatives x)
                                        in
                                          case (findCommon(posLst,negLst))
                                            of NONE => (SOME (CLS (posLst @ negLst)))
                                            | SOME atm => NONE
                                        end
  fun simplify (CNF(x): Cnf): Cnf = CNF(foldl (fn (elem,acc) => case (simplifyClause elem)
                                                                  of SOME a => acc@[a]
                                                                  | NONE => acc)
                                        [] x)
  fun selectResolveAtom (CNF(x): Cnf): string option = let
          val posLst = remDupl(foldl (fn ((CLS(elem)),acc) => (positives elem)@acc) [] x)
          val negLst = remDupl(foldl (fn ((CLS(elem)),acc) => (negatives elem)@acc) [] x)
          in
            (findCommon (posLst,negLst))
          end

  fun mergeClause (a,[],acc) = acc
  |   mergeClause (CLS(x),CLS(y)::tl,acc) = mergeClause(CLS(x),tl,CLS(x@y)::acc)

  fun permutClauseLst ([],lst2,acc) = acc
  |   permutClauseLst (hd::tl,lst2,acc) = permutClauseLst(tl,lst2,mergeClause(hd,lst2,acc))

  fun resolvent (CNF(x): Cnf) (atm: string): Cnf = let
          val (posClauseLst, tempLst) = foldl (fn (CLS(cl),(posL,resL)) =>
                                                      if (isPresent (P atm) cl) then (CLS(cl)::posL,resL)
                                                      else (posL,CLS(cl)::resL)) ([],[]) x
          val (negClauseLst, restLst) = foldl (fn (CLS(cl),(negL,resL)) =>
                                                      if (isPresent (N atm) cl) then (CLS(cl)::negL,resL)
                                                      else (negL,CLS(cl)::resL)) ([],[]) tempLst
          val newPosLst = map (fn CLS(x) => CLS(removeElem x (P atm))) posClauseLst
          val newNegLst = map (fn CLS(x) => CLS(removeElem x (N atm))) negClauseLst
          val merged = permutClauseLst(newPosLst,newNegLst,[])
          in
            CNF(merged@restLst)
          end

  fun resolve (x: Cnf):bool = let 
                                val simple = simplify x
                              in
                                if (existEmpty x) then false
                                else if (x = (CNF [])) then true
                                else
                                  case (selectResolveAtom simple)
                                    of NONE => true
                                    |  (SOME atm) => (resolve(resolvent simple atm))
                              end

  fun toPrefix toString x = let fun prefix(x) =
  (case x
    of TOP => ( "TRUE" )
    | BOTTOM => ( "FALSE" )
    | ATOM(a) => ( toString(a) )
    | NOT(a) => ( "( NOT ( "^(prefix a)^" ) )" )
    | AND(a,b) => ( "( AND ( "^(prefix a)^" , "^(prefix b)^" ) )" )
    | OR(a,b) => ( "( OR ( "^(prefix a)^" , "^(prefix b)^" ) )" )
    | IMP(a,b) => ( "( IMP ( "^(prefix a)^" , "^(prefix b)^" ) )" )
    | IFF(a,b) => ( "( IFF ( "^(prefix a)^" , "^(prefix b)^" ) )" )
    | ITE(a,b,c) => ( "( ITE ( "^(prefix a)^" , "^(prefix b)^" , "^(prefix c)^" ) )" )
  ) in prefix(x) end

  fun toPostfix toString x = let fun postfix(x) = 
  (case x
    of TOP => ( "TRUE" )
    | BOTTOM => ( "FALSE" )
    | ATOM(a) => ( toString(a) )
    | NOT(a) => ( "( ( "^(postfix a)^" )NOT )" )
    | AND(a,b) => ( "( ( "^(postfix a)^" , "^(postfix b)^" )AND )" )
    | OR(a,b) => ( "( ( "^(postfix a)^" , "^(postfix b)^" )OR )" )
    | IMP(a,b) => ( "( ( "^(postfix a)^" , "^(postfix b)^" )IMP )" )
    | IFF(a,b) => ( "( ( "^(postfix a)^" , "^(postfix b)^" )IFF )" )
    | ITE(a,b,c) => ( "( ( "^(postfix a)^" , "^(postfix b)^" , "^(postfix c)^" )ITE )" )
  ) in postfix(x) end
  
  fun isEqual x y = (x=y)
end
