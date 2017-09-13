CM.make("ast.cm");
fun main () =
    let val (inFile, outFile) = case CommandLine.arguments () of
                              [inFile, outFile] => (inFile, outFile)
                            | _ => raise Fail "Usage: wrapper.sml <inFile> <outFile>"
    in
      let val tree = AST_TREE.compile(inFile) in
        AST_TREE.print_tree(outFile,tree)
      end
    end
val _ = main ();
val _ = OS.Process.exit(OS.Process.success);