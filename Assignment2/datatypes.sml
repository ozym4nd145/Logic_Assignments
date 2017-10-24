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

  val makeCnf: string Prop -> Cnf
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
    | AND(a,b) => OR(a,b)
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
                | SOME CLS([]) => raise False
                | SOME a => [a]
             )
    )
  in CNF(conv x) handle False => CNF([])
  end

  fun cnf (x: string Prop) = flattenAnd (pushOr x)
  fun cnfList (x: string Prop list) = foldl (fn (y, CNF l) => let val CNF(t) = cnf(y) in CNF(l@t) end) (CNF []) x

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
