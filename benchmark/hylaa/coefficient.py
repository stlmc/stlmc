#import sympy
from sympy.parsing.sympy_parser import parse_expr

'''
x, y = sympy.symbols("x, y")
expr = 3 + x + 3 * x - 2 * y
coDict = expr.as_coefficients_dict()
for k in coDict.keys():
    print(type(k))
    print(type(coDict[k]))
    print("end")
'''
a = parse_expr('3 + x + 3 * x - 2 * y', evaluate = True)
print(a)
print(a.as_coefficients_dict())
