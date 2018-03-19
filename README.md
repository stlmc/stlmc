## Syntactic separation of signal temporal logic 

Running these scripts requires the following libraries:

1. [Z3 Python api](https://github.com/Z3Prover/z3)
2. [ANTLR](http://www.antlr.org/) for Python 3

Below is a brief description of some script files:

- [testCon.py](testCon.py): runs monitoring for STL formulas in [testcase2.py](testcase2.py) with respect to random signals.
- [testSym.py](testSym.py): runs bounded model checking for STL formulas in [testcaseSym.py](testcaseSym.py) with respect to a simple model.
- [model.py](model.py): generates an SMT encoding of a thermostat hybrid system from an initial set up to a given bound. 
- [randomSTL.py](randomSTL.py): generates random STL formulas, given a set of atoms.
