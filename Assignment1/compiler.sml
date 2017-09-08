structure AST_TREE :
sig
val compile : string -> string AST_TYPES.Prop
val print_exp : string AST_TYPES.Prop -> unit
end = 
struct
exception ASTError;
fun print_exp(x) = let
  val str = AST_TYPES.toPrefix (fn (x:string) => x) x
  in print(str^"\n")
end
fun compile (fileName) = 
  let val inStream = TextIO.openIn fileName;
      val grab: int->string = fn
              n => if TextIO.endOfStream inStream
                   then ""
                   else TextIO.inputN (inStream,n);
      val printError : string * int *int ->unit = fn
          (msg,line,col) =>
              print (fileName ^"["^Int.toString line ^":"
                      ^Int.toString col^"] "^msg^"\n");
      val (tree,rem) = ASTParser.parse
                      (0,
                      (ASTParser.makeLexer grab fileName),
                      printError,
                      fileName)
          handle ASTParser.ParseError => raise ASTError;
      val _ = TextIO.closeIn inStream;
      val _ = print_exp(tree);
  in tree
  end
end;