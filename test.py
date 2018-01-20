import sys
from antlr4 import *
from syntax.stlLexer import stlLexer
from syntax.stlParser import stlParser
from stlVisitorImpl import stlVisitorImpl

from partition import *
from encoding import *


def parseFormula(fStr:str):
    lexer  = stlLexer(InputStream(fStr))
    stream = CommonTokenStream(lexer)
    parser = stlParser(stream)
    tree   = parser.formula()
    return stlVisitorImpl().visit(tree)


f1 = "[] [0,1] ~p /\ [] =1 q /\ <> (2.1,inf) true \/ (false U [0,4) q)"
f2 = "[] [0,1] (p -> <> [1,2] q)"
f3 = "[] [0,1] (p -> <> [1,2] (q /\ [] [3,4] r))"


if __name__ == '__main__':
    formula = parseFormula(f3)
    print(formula)
    print()

    partition = guessPartition(formula, 10)
    for (k,v) in partition.items():
        print(str(k) + ': ' + ', '.join([str(x) for x in v]))

    fs = fullSeparation(formula, partition)
    #print(fs)
    print(fs.size())

    result = valuation(fs, Interval(True, 0.0, True, 0.0))
    #print(result)
    print(result.size())
