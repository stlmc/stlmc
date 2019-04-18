class Expression():
    
    def __init__(self, ode_var):
        self.op = {
                '+': self.plus,
                '-': self.minus,
                '*': self.mul,
                '/': self.div,
        }
        self.ode_var = ode_var
        self.result = 0.0

    def plus(self, left:float, right:float):
        self.result = left + right

    def minus(self, left:float, right:float):
        self.result = left - right

    def mul(self, left:float, right:float):
        self.result = left * right

    def div(self, left:float, right:float):
        self.result = left / right

    def number(self, n:str):
        self.result = float(n)

    def variable(self, var: str):
        self.result = self.ode_var[var]

    def operator(self, op, left:float , right:float):
        self.op[op](left, right)
