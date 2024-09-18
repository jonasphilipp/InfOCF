
#antlr4 -v 4.9.3 -Dlanguage=Python3 QUERYLexer.g4 
#antlr4 -v 4.9.3 -Dlanguage=Python3 QUERYParser.g4 -visitor 
antlr4 -v 4.13.2 -Dlanguage=Python3 CKB.g4 -visitor -no-listener
