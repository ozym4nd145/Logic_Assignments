structure AST_TREE :
sig
val compile : string -> string AST_TYPES.Prop list
val get_prefix: string AST_TYPES.Prop -> string
val get_postfix: string AST_TYPES.Prop -> string
val print_tree: string * (string AST_TYPES.Prop list) -> unit
end = 
struct
exception ASTError;

fun get_prefix(x) = ((AST_TYPES.toPrefix (fn (x:string) => x) x)^"\n")
fun get_postfix(x) = ((AST_TYPES.toPostfix (fn (x:string) => x) x)^"\n")

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
                      (5,
                      (ASTParser.makeLexer grab fileName),
                      printError,
                      fileName)
          handle ASTParser.ParseError => raise ASTError;
      val _ = TextIO.closeIn inStream;
  in tree
  end
fun print_tree(fileName,tree) = 
    let val fd = TextIO.openOut fileName;
    in
        let fun out_file x = (TextIO.output (fd, x ) handle e => (TextIO.closeOut fd; raise e));
            fun gen_pre_post x = (out_file (get_prefix x); out_file (get_postfix(x)));
            val _ =List.map gen_pre_post tree;
        in
            TextIO.closeOut fd
        end
    end
end