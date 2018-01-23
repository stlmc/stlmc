
from stl import *
from partition import *
from separation import *
from encoding import *


f1 = "[] [0,1] ~p /\ [] =1 q /\ <> (2.1,inf) true \/ (false U [0,4) q)"
f2 = "[] [0,1] (p -> <> [1,2] q)"
f3 = "[] [0,1] (p -> q U [1,2] r)"
f4 = "(<> (1,3] s) R [0,1] (p -> q U [1,2] r)"
f5 = "[] [0,1] (p -> <> [1,2] (q /\ [] [3,4] r))"
f6 = "[] [0,1] (p -> (~r U [1,2] (q /\ [] [3,4] r)))"
f7 = "(<> (1,2) ~r) U [0,1] (p -> (s U [1,2] (q /\ [] [3,4] r)))"


if __name__ == '__main__':
    formula = parseFormula(f3)
    print(formula)
    print()

    (partition,const) = guessPartition(formula, 7)
    for (k,v) in partition.items():
        print(str(k) + ': ' + ', '.join([str(x) for x in v]))

    print("Partition: " + str(sizeAst(And(const))))

    fs = fullSeparation(formula, partition)
    #print(fs)
    print("Separation: " + str(fs.size()))

    result = valuation(fs, baseEncoding(partition), Interval(True, 0.0, True, 0.0))
    #print(result)
    print("Valuation: " + str(sizeAst(result)))

    s = Solver()
    s.add(const)
    s.add(result)
#    print(s.to_smt2())
    print (s.check())
    print (s.model())

