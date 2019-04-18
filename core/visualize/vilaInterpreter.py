import sys
from antlr4 import *
from vila.vilaLexer import vilaLexer
from vila.vilaParser import vilaParser
from vila.vilaVisitor import vilaVisitor
import numpy as np
from scipy.integrate import odeint
import matplotlib.pyplot as plt


class VilaInterpreter():

    def __init__(self):
        self.input
        self.input = InputStream("")
        self.lexer = vilaLexer(input)
        self.stream = CommonTokenStream(lexer)
        self.parser = vilaParser(stream)
        self.tree = parser.statement()
        self.vila = vilaVisitor({'none':0}).visit(tree)


    # _readVila for internal supported
    # var_assn: ode variable list in dictionary form
    # e.g) z = { 'x1': 0, 'x2' :1 }
    def _readVila(self, var_assn, vila_string:str):
        self.input = InputStream(vila_string)
        self.lexer = vilaLexer(input)
        self.stream = CommonTokenStream(lexer)
        self.parser = vilaParser(stream)
        self.tree = parser.statement()
        self.vila = vilaVisitor(var_assn).visit(tree)
        return self.vila

    def vila2model(self, var_assn, vila_string_list:list):
        return [ self._readVila(var_assn, vila_string).result for vila_string in vila_string_list ]
        

        




'''
def model(z, t):
    input = InputStream("3*x1 + 2*x2")
    input2 = InputStream("x1 + 0.5*x2")
    lexer = toyLexer(input)
    lexer2 = toyLexer(input2)
    stream = CommonTokenStream(lexer)
    stream2 = CommonTokenStream(lexer2)
    parser = toyParser(stream)
    parser2 = toyParser(stream2)
    tree = parser.statement()
    tree2 = parser2.statement()
    za = { 
            'x1': z[0], 
            'x2': z[1] 
        }
    mathT = mathVisitor(za).visit(tree)
    mathT2 = mathVisitor(za).visit(tree2)
    res = mathT.result
    res2 = mathT2.result
    return [res, res2]

z0 = [0 , 1]

t = np.linspace(0, 2500)
'''
'''
def main(argv):
    
    z = odeint(model, z0, t)

    # plot results
    plt.plot(t,z[:,0],'b-',label=r'$\frac{dx}{dt}=3x_1 + 2x_2$')
    plt.plot(t,z[:,1],'r--',label=r'$\frac{dy}{dt}=x_1+0.5x_2$')
    plt.ylabel('variables')
    plt.xlabel('time')
    plt.legend(loc='best')
    plt.show()
    
    
    
    input = FileStream(argv[1])
    input = InputStream("2")
    lexer = toyLexer(input)
    stream = CommonTokenStream(lexer)
    parser = toyParser(stream)
    tree = parser.statement()
    z_initial = [0.0, 1.0, 2.0, 3.0]
    z = {
            'x1' : z_initial[0],
            'x2' : z_initial[1],
            'constx1' : z_initial[2],
            'constx2' : z_initial[3],
            }
    mathT = mathVisitor(z).visit(tree)
    print("result : " + str(mathT.result))


if __name__ == '__main__':
    main(sys.argv)
'''
