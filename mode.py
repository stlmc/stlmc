
def modeToVal(arg):
    result = []
    while arg > 0:
        result.append(arg % 2)
        arg = arg // 2
    return result

def modeVal(*args):
    value = 0
    for i in range(len(args)):
        if args[i] == 1:
           value += pow(2, i)
    return value

def totalMode(*args):
    return pow(2, len(args))



