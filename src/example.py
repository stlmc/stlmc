from stlMC import *

# taylor approximation of trigonometric functions
def sin(degree):
    return degree - degree * degree * degree / RealVal(6)

def cos(degree):
    return degree - degree * degree / RealVal(2)

def tan(degree):
    return degree + degree * degree * degree

# some constants
L1 = RealVal(0.8)
ZERO = RealVal(0)

# a hybrid automaton for a single car
class SingleCar(Model):

    def __init__(self):
        # modes
        mf = Bool('mf')
        ms = Bool('ms')

        # variables
        x = Real('x')
        y = Real('y')
        v = Real('v')
        phi = Real('phi')
        theta = Real('theta')
        constv = Real('constv')
        constphi = Real('constphi')
        consttheta = Real('consttheta')

        # flow conditions
        flowx = constv * cos(consttheta)
        flowy = constv * sin(consttheta)
        flowtheta = constv / L1 * tan(constphi)
        flowphi = ZERO

        flow = { \
                And(Not(mf), Not(ms)): \
                {x: flowx, y: flowy, theta: flowtheta, phi: flowphi,v: ZERO, constv: ZERO, constphi: ZERO, consttheta: ZERO}, \
                \
                And(Not(mf), ms): \
                {x: flowx, y: flowy, theta: flowtheta, phi: flowphi,v: ZERO, constv: ZERO, constphi: ZERO, consttheta: ZERO}, \
                \
                And(mf, Not(ms)): \
                {x: flowx, y: flowy, theta: flowtheta, phi: flowphi,v: ZERO, constv: ZERO, constphi: ZERO, consttheta: ZERO}} 

        # initial conditions
        init = And(And(Not(mf), Not(ms)), x > RealVal(0), x < RealVal(3), y < RealVal(10), y > RealVal(3), v >= RealVal(1), v <= RealVal(3), theta > RealVal(0), theta < RealVal(1), phi <= RealVal(1), phi >= RealVal(0), And(constv == v, constphi == phi, consttheta == theta))


        # set the interval bound to the variables
        vars = {x: (0, 100), y: (0, 100), v: (0, 10), theta: (-1.5, 1.5), phi: (-1, 1)}
        # invariant conditions
        inv = {And(Not(mf), Not(ms)): BoolVal(True), \
               And(Not(mf), ms): BoolVal(True), \
               And(mf, Not(ms)): BoolVal(True)}

        # jump conditions
        mfNext = NextVar(mf)
        msNext = NextVar(ms)
        xNext = NextVar(x)
        yNext = NextVar(y)
        vNext = NextVar(v)
        phiNext = NextVar(phi)
        thetaNext = NextVar(theta)
        constvNext = NextVar(constv)
        constphiNext = NextVar(constphi)
        constthetaNext = NextVar(consttheta)

        jump = {\
                And(Not(mf), Not(ms), theta < RealVal(10)): \
                And(And(mfNext, Not(msNext)), vNext == RealVal(7), xNext == x, yNext == y, phiNext == phi, thetaNext == theta, And(constv == v, constphi == phi, consttheta == theta)), \
                \
                And(Not(mf), Not(ms), theta > RealVal(30)): \
                And(And(mfNext, msNext), vNext == RealVal(-5), xNext == x, yNext == y, phiNext == phi, thetaNext == theta, And(constv == v, constphi == phi, consttheta == theta)), \
                \
                And(Not(mf), ms, theta >= RealVal(10), theta <= RealVal(30)): \
                And(Not(mf), Not(ms), vNext == RealVal(2), xNext == x, yNext == y, phiNext == phi, thetaNext == theta, And(constv == v, constphi == phi, consttheta == theta)), \
                \
                And(Not(mf), ms, theta < RealVal(10)): \
                And(And(mfNext, Not(msNext)), vNext == RealVal(7), xNext == x, yNext == y, phiNext == phi, thetaNext == theta, And(constv == v, constphi == phi, consttheta == theta)), \
                \
                And(mf, Not(ms), theta >= RealVal(10), theta <= RealVal(30)): \
                And(Not(mf), Not(ms), vNext == RealVal(2), xNext == x, yNext == y, phiNext == phi, thetaNext == theta, And(constv == v, constphi == phi, consttheta == theta)), \
                \
                And(mf, Not(ms), theta < RealVal(10)): \
                And(And(Not(mfNext), msNext), vNext == RealVal(7), xNext == x, yNext == y, phiNext == phi, thetaNext == theta, And(constv == v, constphi == phi, consttheta == theta))}


        # STL propositions
        propLeft = Bool('propleft')
        propRight = Bool('propright')
        propTemp = Bool('propTemp')
        prop = {propTemp: mf, propLeft: v < RealVal(180), propRight: phi < RealVal(60)}

        super().__init__(vars, init, flow, inv, jump, prop)


if __name__ == '__main__':
    model = SingleCar()

    # STL model checking 
#    formula = "[][0.0,60.0] (propleft /\ propright)"
    formula = "<>[0.0, 60.0] proTemp"
    print("model checking: " + str(formula))
    (result, cSize, fsSize, gTime, sTime, tTime)  = model.modelCheck(formula, 2, 60)
    print("    result: %s (constration size = %d, translation size = %d)" % (str(result), cSize, fsSize))


    # reachability analysis
#    goal  = And(Real('x') == RealVal(50), Real('y') == RealVal(100))
    goal = Not(Bool('mf'))
    print("reachability checking: " + str(goal))
    result = model.reach(10, goal)
    print("    result: %s (constration size = %d)" % result)


