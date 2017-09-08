structure ASTLrVals = ASTLrValsFun(
                structure Token = LrParser.Token);
structure ASTLex = ASTLexFun(
                structure Tokens = ASTLrVals.Tokens);
structure ASTParser = JoinWithArg(
                structure ParserData = ASTLrVals.ParserData
                structure Lex = ASTLex
                structure LrParser = LrParser);
