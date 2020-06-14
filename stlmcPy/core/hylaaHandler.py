import itertools
from functools import singledispatch
from .model import *
from .node import *
from .z3Handler import *

from matplotlib import collections

from sympy.parsing.sympy_parser import parse_expr

from hylaa.hybrid_automaton import HybridAutomaton
from hylaa.settings import HylaaSettings, PlotSettings, LabelSettings
from hylaa.core import Core
from hylaa.aggstrat import Aggregated
from hylaa.stateset import StateSet
from hylaa import lputil, symbolic

@singledispatch
def orClause(const:Node):
    return [const]

@orClause.register(And)
def _(const):
    result = list()
    for c in list(const.children):
        if isinstance(c, Or):
            result.extend(orClause(c))
    return result

@orClause.register(Or)
def _(const):
    result = list()
    for c in list(const.children):
        result.extend(orClause(c))
    return result

@orClause.register(Not)
def _(const):
    result = list()
    result.extend(const.child())
    return result

@singledispatch
def timeClause(const:Node):
    subVars = list(const.getVars())
    timeList = [s for s in subVars if 'tau_' in str(s)]
    tc = True if len(timeList) > 0 else 0
    result = list()
    if tc:
        return [const]
    return result

@timeClause.register(And)
def _(const):
    subVars = list(const.getVars())
    timeList = [s for s in subVars if 'tau_' in str(s)]
    tc = True if len(timeList) > 0 else 0
    result = list()
    if tc:
        for x in const.children:
            result.extend(timeClause(x))
    contVarList = ['tau']
    tlist = [x for x in result if determine(x, contVarList)]
    return tlist

@timeClause.register(Implies)
def _(const):
    subVars = list(const.getVars())
    timeList = [s for s in subVars if 'tau_' in str(s)]
    tc = True if len(timeList) > 0 else 0
    result = list()
    if tc:
        result = timeClause(const.left())
        result.extend(timeClause(const.right()))
    return result

@timeClause.register(Or)
def _(const):
    subVars = list(const.getVars())
    timeList = [s for s in subVars if 'tau_' in str(s)]
    tc = True if len(timeList) > 0 else 0
    result = list()
    if tc:
        for x in const.children:
            result.extend(timeClause(x))
        contVarList = ['tau']
        tlist = [x for x in result if determine(x, contVarList)]
        #result = [tlist[0]]
        result = tlist
    return result

@timeClause.register(Not)
def _(const):
    subVars = list(const.getVars())
    timeList = [s for s in subVars if 'tau_' in str(s)]
    tc = True if len(timeList) > 0 else 0
    result = list()
    if tc:

        result.extend(timeClause(const.child()))
    return result


@singledispatch
def clause(const:Node):
    return [const]

@clause.register(And)
def _(const):
    result = list()
    for c in list(const.children):
        result.extend(clause(c))
    return result

@clause.register(Or)
def _(const):
    result = list()
    for c in list(const.children):
        result.extend(clause(c))
    return result

@clause.register(Not)
def _(const):
    result = list()
    result.extend(clause(const.child()))
    return result

def determine(form, strContVars):
    subVars = list(form.getVars())
    for sv in subVars:
        if isinstance(sv.id, Bool):
            return False
        else:
            strv = str(sv.id)
            
            vid = strv[0:strv.find('_')]
            v0 = strv[0:-2]
            
            if not (vid in strContVars) and not (v0 in strContVars):
                return False
    return True

def isGuard(form):
    subVars = list(form.getVars())
    for sv in subVars:
        strv = str(sv.id)
        flag = strv[-1]
        if (flag == '0'):
            return False
    return True

def coreConsts(allConsts, contVarList, model):
    literals = list()
    for c in allConsts:
        literals.extend(clause(c))
    
    clist = [x for x in literals if determine(x, contVarList)]
    #clist = [x for x in clist if not isinstance(x, Forall)]
    tl = [x for x in literals if model.eval(z3Obj(x))]
    fl = [Not(x) for x in literals if not model.eval(z3Obj(x))]
    total = tl + fl
    z3Consts=[z3Obj(c) for c in total]
    z3allConsts = [z3Obj(c) for c in allConsts]
     
    #print(z3.simplify(z3.Implies(z3.And(*z3Consts), z3.And(*z3allConsts))))
    print(z3.simplify(z3.Implies(z3.simplify(z3.And(*z3Consts)), z3.simplify(z3.And(*z3allConsts)))))



def checkHylaa(solver, consts, modeModules, modeVars, contVars, transReaches, usedProp, timeConstraints, bound, delta):
    initValList = list()
    m = solver.model()
    allConsts = list()
    
    for i in consts:
        allConsts.extend(clause(i))
  
    allConsts = [x for x in allConsts if not isinstance(x, Forall)]
    allConsts = [x if m.eval(z3Obj(x)) else Not(x) for x in allConsts]

    timeConsts = [x for x in timeConstraints if m.eval(z3Obj(x))]

    numModes = list()
    for i in range(bound + 1):
        modeVar = z3.Real('currentMode_' + str(i))
        numModes.append(m[modeVar])
        allConsts.append(Real('currentMode_' + str(i)) == RealVal(int(str(m[modeVar]))))

    contVarList = list()
    for j in range(bound + 1):
        for i in range(len(contVars)):
            contVarList.append(str(contVars[i].id) + "_" + str(j))

    for j in range(bound + 1):
        contVarList.append("tau_" + str(j))
    
    for i in range(len(contVars)):
        contVarList.append(str(contVars[i].id) + "_" + str(bound + 1))
    #contVarList.append('constant_value')

    for contIndex in range(len(contVars)):
        op = {'bool': z3.Bool, 'int': z3.Int, 'real': z3.Real}
        curCont = contVars[contIndex]
        initial_var = op[curCont.type](str(curCont.id) + "_" + str(0) + "_0")
        initVal = float(m[initial_var].as_decimal(6).replace("?", ""))
        initValList.append((initVal, initVal))

    # For time variables (tau_0, ...) which represent global time points
    for i in range(len(contVars), len(contVarList)):
        initValList.append((0,0))

    # For constant
    initValList.append((1,1))
    
    (jumpScenario, ha) = make_automaton(m, numModes, modeModules, len(contVars), modeVars, contVarList, transReaches, usedProp, timeConsts, delta)

    allConsts.extend(jumpScenario)

    init_states = make_init(ha, initValList)
    
    settings = make_settings()

    #coreConsts(consts, contVarList, m)
    ce = Core(ha, settings).run(init_states)

    #result = ce.last_cur_state.mode.name
    result = 'error'
    

    return (result, allConsts)



def hylaaModel(allconsts, modeVars, contVars, bound, modeModules, reach, delta, propList):
    (timeConsts, hybridconsts) = allconsts
    transReaches = list()
    for i in range(0, bound + 1):
        varDict = dict()
        for j in range(len(contVars)):
            varDict[str(contVars[j].id)] = Real(contVars[j].id + '_' + str(i))
        transReaches.append(clause(reach.getExpression(varDict)))
    #print("allConsts")
    #print(consts) 

    consts = hybridconsts + timeConsts
    z3Consts = [z3Obj(c, True) for c in consts]

    solver = z3.Solver()
    solver.add(z3Consts)
    '''
    with open("thermoLinear.smt2", 'w') as fle:
        print(solver.to_smt2(), file=fle)

    '''
    tc = list() 
    for x in timeConsts:
        tc = tc + timeClause(x)

    result = solver.check()
    usedProp = dict()
    if str(result) == "sat":
        m = solver.model()
        for pid in propList:
            propVar = z3.Bool(pid.id + "_0")
            if m[propVar] is not None:
                subresult = list()
                for b in range(bound + 1):
                    subresult.append(m[z3.Bool(pid.id + "_" + str(b))])
                usedProp[pid] = subresult

        (reachable, allConsts) = checkHylaa(solver, consts, modeModules, modeVars, contVars, transReaches, usedProp, tc, bound, delta)
        out = 0
        while not (reachable == 'error') and out < 2:
            newScenario = list()
            newScenario.append(Not(And(*allConsts)))
            newScenario.extend(consts)

            z3Consts = [z3Obj(c, True) for c in newScenario]

            solver = z3.Solver()
            solver.add(z3Consts)
            result = solver.check()

            if not str(result) == "sat":
                break
            (reachable, allConsts) = checkHylaa(solver, newScenario, modeModules, modeVars, contVars, transReaches, usedProp, tc, bound, delta)
            consts = newScenario
            out = out + 1

    else:
        m = None
        raise ("No transition exists")
    result = False
    cSize = -1
    return (result, cSize)

def makeSubMode(modeVars, k):
    op = {'bool': Bool, 'int': Int, 'real': Real}
    result = {}
    for i in range(len(modeVars)):
        result[str(modeVars[i].id)] = op[modeVars[i].type](modeVars[i].id + '_' + str(k))
    return result

def make_automaton(model, numModes, modeModules, numContVars, modeVarList, contVarList, reaches, usedProp, timeConstraints, delta):
    timeConstraints = list(dict.fromkeys(timeConstraints))
    ha = HybridAutomaton('Hybrid automata')
    # i is the current bound
    for i in range(len(numModes)):
        m = ha.new_mode('Mode_' + str(i))
        #print("current Mode")
        ##print(numModes[i])
        flowExp = modeModules[int(numModes[i].as_decimal(6).replace("?", ""))].getFlow().exp()

        flowList = list()
        flowList = ['0'] * len(contVarList)

        for k in range(len(flowExp)):
            for j in range(i * numContVars, (i + 1) * numContVars): 
                sliceIndex = contVarList[j].find("_")
                if contVarList[j][0:sliceIndex] == flowExp[k].getVarId():
                    flowList[j] = flowExp[k].flow.infix()

        curTauInd = contVarList.index('tau_' + str(i))
        for j in range((i+1) * numContVars, len(contVarList) - numContVars):
            if j >= curTauInd:
                flowList[j] = '1'

        constant_dict = dict()

        a_mat = symbolic.make_dynamics_mat(contVarList, flowList, constant_dict, has_affine_variable=True)

        m.set_dynamics(a_mat)

        invExp = modeModules[int(numModes[i].as_decimal(6).replace("?", ""))].getInv()
        jumpExp =  modeModules[int(numModes[i].as_decimal(6).replace("?", ""))].getJump()

        subDict = dict()
        nextDict = dict()
        subvars = dict()
        subJump = dict()
        for q in range(i * numContVars, (i + 1) * numContVars):
            sliceIndex = contVarList[q].find("_")
            subDict[contVarList[q][0:sliceIndex]] = Real(contVarList[q])
            subvars[contVarList[q][0:sliceIndex]] = Real(contVarList[q][0:sliceIndex])
            subJump[contVarList[q][0:sliceIndex]] = Real(contVarList[q] + "_t")
            nextDict[contVarList[q][0:sliceIndex]] = Real(contVarList[q][0:sliceIndex] + "_" + str(i+1) + "_0") 

        invExp = invExp.getExpression(subDict)
        invariants = [x.infixExp(delta) for x in clause(invExp)]
        for up in usedProp.keys():
            curVal = usedProp[up][i]
            curExp = up.cond.getExpression(subDict)
            propExp = curExp if curVal else Not(curExp).reduce()
            strProp = propExp.infixExp(delta)
            invariants.append(strProp)
        
        cptimeConsts = list()
        for tn in range(len(timeConstraints)):
            tc = timeConstraints[tn]
            variables = list(tc.getVars())
            maxVal = 0
            for vt in variables:
                sliceIndex = str(vt).find("_")
                newVal = int(str(vt)[sliceIndex+1:])
                maxVal = newVal if newVal > maxVal else maxVal
            if str(maxVal + 1) == str(i):
                invariants.append(tc.infixExp(delta))
                cptimeConsts.append(tc)

        invariants = ' & '.join(invariants)

        if len(invariants) > 0:
            mat, rhs = symbolic.make_condition(contVarList, invariants.split('&'), constant_dict, has_affine_variable=True)
            m.set_invariant(mat, rhs)

        jumpList = jumpExp.getRedeclList()
        
        op = {'bool': Bool, 'int': Int, 'real': Real}
        subMode =dict()
        nextMode = dict()
        for q in modeVarList:
            subvars[str(q.id)] = op[q.type](q.id)
            subMode[str(q.id)] = op[q.type](q.id + '_' + str(i))
            nextMode[str(q.id)] = op[q.type](q.id + '_' + str(i + 1))
        subvars['false'] = BoolVal(False)
        subvars['true'] = BoolVal(True)

        subJump.update(subMode)
        nextDict.update(nextMode)
        curJump = list()
       
        for jl in jumpList:
            jl = jl.getExpression(subvars)
            jump = jl.substitution(subJump)
            curJump.append(jump.nextSub(nextDict))
        jumpScenario = [Not(x) for x in curJump if not model.eval(z3Obj(x))]
        satJump = [x for x in curJump if model.eval(z3Obj(x))]
        
        if len(satJump) >= 1:
            if len(satJump) > 1:
                jumpScenario.extend([Not(x) for x in satJump[1:]])
            clist = clause(satJump[0])
            orList = orClause(satJump[0])
            
            clist = [x for x in clist if determine(x, contVarList)]
            guard = [x for x in clist if isGuard(x)]
            reset = [x for x in clist if not isGuard(x)]
            guard = [x for x in guard if model.eval(z3Obj(x))]
            reset= [x for x in reset if model.eval(z3Obj(x))]
           
            flag = 0
            if len(orList) > 1:
                jumpScenario.extend(guard)
                for ol in orList:
                    for gl in range(len(guard)):
                        if str(ol) == str(guard[gl]):
                            flag = 1
                            break
                    if flag == 0:
                        jumpScenario.append(Not(ol))
                    flag = 0
                        
                jumpScenario.extend(reset)
            else:
                jumpScenario.append(satJump[0])
            
                    
        else:
            guard = list()
            reset = list()

    m = ha.new_mode('error')
    flowList = [[0 for x in range(len(contVarList))] for y in range(len(contVarList))]
    m.set_dynamics(flowList)

    for i in range(len(numModes)):
        pre = ha.modes['Mode_' + str(i)]
        post = ha.modes['error']
        t = ha.new_transition(pre, post)
        guardConds = [x.infixExp(delta) for x in reaches[i]]
        guardConds = ' & '.join(guardConds)
        mat, rhs = symbolic.make_condition(contVarList, guardConds.split('&'), constant_dict, has_affine_variable=True)

        t.set_guard(mat, rhs)
        resetList = ['0'] * (len(contVarList) - 1)
        
        for ri in range(len(contVarList) - 1):
            resetList[ri] = contVarList[ri]
        
        reset_mat = symbolic.make_reset_mat(contVarList, resetList, constant_dict, has_affine_variable=True)
        
        t.set_reset(reset_mat)

    subDict = dict()
    for q in range(0, len(numModes) * numContVars) :
        subDict[contVarList[q] + '_t'] = Real(contVarList[q])

    for i in range(len(numModes) - 1):
        pre = ha.modes['Mode_' + str(i)]
        post = ha.modes['Mode_' + str(i+1)]
        t = ha.new_transition(pre, post)
        guard = [x.substitution(subDict) for x in guard]
        guardConds = [x.infixExp(delta) for x in guard]
        guardConds = ' & '.join(guardConds)
        mat, rhs = symbolic.make_condition(contVarList, guardConds.split('&'), constant_dict, has_affine_variable=True)
        t.set_guard(mat, rhs)            


        resetList = list()
        resetList = ['0'] * len(contVarList) 
       
        for ri in range(len(reset) - numContVars):
            r = reset[ri]
            resetList[ri] = r.substitution(subDict).right().infix()

        for ri in range(len(numModes) * numContVars, len(contVarList)):
            resetList[ri] = contVarList[ri]
        
        reset_mat = symbolic.make_reset_mat(contVarList, resetList, constant_dict, has_affine_variable=True)
     
        t.set_reset(reset_mat)



    return (jumpScenario, ha)

def make_init(ha, initVal):
    mode = ha.modes['Mode_' + str(0)]
    init_lpi = lputil.from_box(initVal, mode)
    
    init_list = [StateSet(init_lpi, mode)]
    
    return init_list

def make_settings():
    'make the reachability settings object'

    # see hylaa.settings for a list of reachability settings
    # step_size = 0.1, max_time = 10
    settings = HylaaSettings(0.1, 100)
    settings.stop_on_aggregated_error = False
    settings.process_urgent_guards = True

    #settings.aggstrat = MyAggergated()
    settings.aggstrat.deaggregate = True # use deaggregation
    settings.aggstrat.deagg_preference = Aggregated.DEAGG_LEAVES_FIRST

    settings.plot.plot_mode = PlotSettings.PLOT_IMAGE
    #settings.stdout = HylaaSettings.STDOUT_VERBOSE

    settings.plot.filename = "demo_reset.png"

    return settings
