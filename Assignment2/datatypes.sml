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

  exception Empty
  exception False

  val makeCnf: string Prop -> Cnf
  val resolve: Cnf -> bool

  fun baseProp (x: 'a Prop) -> 'a Prop = 
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

  fun nnf (x: 'a Prop) -> 'a Prop =
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

  fun pushOr (x: 'a Prop) -> 'a Prop = 
  (case (nnf x)
    of TOP => TOP
    | BOTTOM => BOTTOM
    | ATOM(a) => ATOM(a)
    | NOT(ATOM(a)) => NOT(ATOM(a))
    | AND(a,b) => OR(a,b)
    | OR(AND(a,b),c) => AND(pushOr(OR(a,c)),pushOr(OR(b,c)))
    | OR(c,AND(a,b)) => pushOr (OR(AND(a,b),c))
    | OR(a,b) => OR(pushOr a,pushOr b)
    | _       => raise Error("Input Proposition is not of nnf form")
  )

  fun flattenAnd (x: string Prop) -> Clause = 
    let
      fun conv(x) = (case x
        of TOP => []
        |  BOTTOM => raise False
        |  ATOM(a) => [P(a)]
        |  NOT(ATOM(a)) => [N(a)]
        |  AND(a,TOP) => flattenAnd(a)
        |  AND(TOP,a) => flattenAnd(AND(a,TOP))
        |  AND(a,b) => flattenAnd(a)@flattenAnd(b)
      )
    in (case conv(x)
          of [] => raise Empty
          | a => a
       ) handle False => []
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
