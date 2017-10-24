CM.make("ast.cm");
fun main () =
    let val (inFile, outFile) = case CommandLine.arguments () of
                              [inFile, outFile] => (inFile, outFile)
                            | _ => raise Fail "Usage: wrapper.sml <inFile> <outFile>"
    in
      let
        val tree = AST_TREE.compile(inFile)
        val _ = AST_TREE.print_tree(outFile,tree)
        val cnf = AST_TREE.makeCnf(tree)
        val satisfiable = AST_TREE.resolve(cnf)
        val _ = print("#################################################\n")
        val _ = print("############ Satisfiability: " ^ (Bool.toString satisfiable) ^ " ###############\n")
      in
        print("#################################################\n")
      end
    end
val _ = main ();
val _ = OS.Process.exit(OS.Process.success);