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
