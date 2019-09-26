import json

'''
{"data": [ [0.0, 1.0], [0.15701402040816326, 11.205911326530611] ], "proplist": { "disl10": "x2-x1 < 10" }, "prop": { "disl10":["True", "True", "True", "True", "True", "True", "True", "True", "True", "True", "True"] }}
'''

def genDataPair(data_name, start, end):
    res = []
    for i in range(start, end):
        pair = [i, i + 1]
        res.append(pair)
    d = dict()
    d[data_name] = res
    return d

def genProp(name, len):
    res = []
    for i in range(len):
        if i%2 == 0:
            res.append("True")
        else:
            res.append("False")
    resP = dict()
    resP[name] = res
    return resP

data_size = 100000

def genData(data_name, prop_name, data_len, interval_len):
    data = dict()
    dataArray = []
    for i in range(interval_len):
        dataArray.append(genDataPair(data_name, i * data_len, (i + 1) * data_len))
    data['data'] = dataArray
    data['proplist'] = {}
    data['prop'] = genProp(prop_name, interval_len)
    f = open(("test"+ str(data_len) +".json"), "w")
    json.dump(data, f)
    f.close()


genData("x1", "testprop", 10000, 12)