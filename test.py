import sys
from antlr4 import *
from syntax.stlLexer import stlLexer
from syntax.stlParser import stlParser
from stlVisitorImpl import stlVisitorImpl

from partition import *
from separation import *
from encoding import *


def parseFormula(fStr:str):
    lexer  = stlLexer(InputStream(fStr))
    stream = CommonTokenStream(lexer)
    parser = stlParser(stream)
    tree   = parser.formula()
    return stlVisitorImpl().visit(tree)



f1 = "[] [0,1] ~p /\ [] =1 q /\ <> (2.1,inf) true \/ (false U [0,4) q)"
f2 = "[] [0,1] (p -> <> [1,2] q)"
f3 = "[] [0,1] (p -> q U [1,2] r)"
f4 = "(<> (1,3] s) R [0,1] (p -> q U [1,2] r)"
f5 = "[] [0,1] (p -> <> [1,2] (q /\ [] [3,4] r))"
f6 = "[] [0,1] (p -> (~r U [1,2] (q /\ [] [3,4] r)))"
f7 = "(<> (1,2) ~r) U [0,1] (p -> (s U [1,2] (q /\ [] [3,4] r)))"


if __name__ == '__main__':
    formula = parseFormula(f2)
    print(formula)
    print()

    partition = guessPartition(formula, 10)
    for (k,v) in partition.items():
        print(str(k) + ': ' + ', '.join([str(x) for x in v]))

    fs = fullSeparation(formula, partition)
    #print(fs)
    print(fs.size())

    result = valuation(fs, Interval(True, 0.0, True, 0.0))
    print(result)
    print(result.size())

