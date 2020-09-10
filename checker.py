import sys
import re
import math


def readFile(traceFile):
    numProcess = 0
    EventList = []
    EName = []
    ETime = []
    EValue = []
    EType = []
    name = 1
    ENameAll = []
    ETimeAll = []
    EValueAll = []
    ETypeAll = []
    file = open(traceFile, "r")
    for line in file:
        words = line.split('\"')
        if "\\Process" in words[0]:
            ENameAll.append(EName)
            ETimeAll.append(ETime)
            EValueAll.append(EValue)
            ETypeAll.append(EType)
            numProcess = numProcess + 1
            EName = []
            ETime = []
            EValue = []
            EType = []
        elif "Event" in words[0]:
            EName.append(name)
            name = name + 1
            EType.append(words[3])
            EValue.append(words[5])
            ETime.append(words[7])
    return ENameAll, ETimeAll, EValueAll, ETypeAll


def convertToNum(words, pos, AP):
    p2 = words.find("=", pos)
    num = list()
    for w2 in words[p2 + 2:].split("||"):
        num1 = 0
        if w2 == "<empty>":
            num1 = 0
        else:
            for w3 in w2.split("&&"):
                # print(AP.find(w3))
                w3 = w3.strip()
                x = len(AP) - AP.find(w3) - 1
                # print(x)
                # if "p" in w3:
                #     x = 2
                # elif "q" in w3:
                #     x = 1
                # elif "r" in w3:
                #     x = 0
                num1 = num1 + int(pow(2, x))
        num.append(num1)
    # print(num)
    return num


def createSMT(formula, variables, AP):
    finalFormula = ""
    for w1 in formula[:-4].split(", "):
        print(w1)
        if w1[0] == 'E':
            sw1 = "Exists("
            p1 = w1.find(".")
            if p1 <= 6:
                sw1 = sw1 + w1[1:p1] + ", Implies(" + w1[1:p1] + " >= 0, Or(False"
                num = convertToNum(w1, p1, AP)
                for x in num:
                    sw1 = sw1 + ", BV2Int(valMap(v1) | valMap(v2)) == " + str(x)
                sw1 = sw1 + "))"
            elif 6 < p1 <= 16:
                p2 = w1.find("=")
                sw1 = sw1 + w1[1:p2-1] + ", Implies(" + w1[1:p2-1] + " == " + w1[p2+2:p1-2] + " - 1, Or(False"
                num = convertToNum(w1, p1, AP)
                for x in num:
                    sw1 = sw1 + ", BV2Int(valMap(v1) | valMap(v2)) == " + str(x)
                sw1 = sw1 + "))"
            else:
                p2 = w1.find("<=")
                p3 = w1.find("<", p2 + 2)
                sw1 = sw1 + w1[p2 + 3:p3 - 1] + ", Implies( And(" + w1[1:p2 - 1] + " <= " + w1[p2 + 3:p3 - 1] + ", " + w1[p2 + 3:p3 - 1] + " < " + w1[p3 + 2:p1] + "), Or(False,"
                num = convertToNum(w1, p1, AP)
                for x in num:
                    sw1 = sw1 + ", BV2Int(valMap(v1) | valMap(v2)) == " + str(x)
                sw1 = sw1 + "))"
            sw1 = sw1 + ")"
        elif w1[0] == 'A':
            sw1 = "ForAll("
            p1 = w1.find(".")
            if p1 <= 6:
                sw1 = sw1 + w1[1:p1] + ", Implies(" + w1[1:p1] + " >= 0, Or(False,"
                num = convertToNum(w1, p1, AP)
                for x in num:
                    sw1 = sw1 + ", BV2Int(valMap(v1) | valMap(v2)) == " + str(x)
                sw1 = sw1 + "))"
            elif 6 < p1 <= 16:
                p2 = w1.find("=")
                sw1 = sw1 + w1[1:p2 - 1] + ", Implies(" + w1[1:p2 - 1] + " == " + w1[p2 + 2:p1-2] + " - 1, Or(False"
                num = convertToNum(w1, p1, AP)
                for x in num:
                    sw1 = sw1 + ", BV2Int(valMap(v1) | valMap(v2)) == " + str(x)
                sw1 = sw1 + "))"
            else:
                p2 = w1.find("<=")
                p3 = w1.find("<", p2 + 2)
                sw1 = sw1 + w1[p2 + 3:p3 - 1] + ", Implies( And(" + w1[1:p2 - 1] + " <= " + w1[p2 + 3:p3 - 1] + ", " + w1[p2 + 3:p3 - 1] + " < " + w1[p3 + 2:p1] + "), Or(False"
                num = convertToNum(w1, p1, AP)
                for x in num:
                    sw1 = sw1 + ", BV2Int(valMap(v1) | valMap(v2)) == " + str(x)
                sw1 = sw1 + "))"
            sw1 = sw1 + ")"
        else:
            p2 = w1.find("=")
            sw1 = w1[:p2-1] + " == 0"
        print(sw1)
        finalFormula = finalFormula + ", " + sw1
    return finalFormula


def main(traceFile, writeFile, smtFormula, fileNum):
    ENameAll, ETimeAll, EValueAll, ETypeAll = readFile(traceFile)
    # print(ETimeAll)
    setEvent = []
    for a in ENameAll:
        for b in a:
            setEvent.append(b)
    # pwSetEvent = makePowerSet(setEvent, len(setEvent))
    # print(pwSetEvent)
    # enPwSetEvent = encodePowerSet(pwSetEvent, len(setEvent))
    # print(enPwSetEvent)

    setHb = []
    for a in ENameAll:
        for i in range(0, len(a) - 1):
            hb = [a[i], a[i + 1]]
            setHb.append(hb)
    for i in range(len(ENameAll)):
        for ii in range(len(ENameAll[i])):
            for j in range(0, len(ENameAll)):
                if i == j:
                    continue
                for jj in range(len(ENameAll[j])):
                    time1 = int(ETimeAll[i][ii].split(", ")[0][1:])
                    time2 = int(ETimeAll[j][jj].split(", ")[0][1:])
                    if time2 - time1 >= eps:
                        hb = [ENameAll[i][ii], ENameAll[j][jj]]
                        # print(hb)
                        setHb.append(hb)
    for i in range(0, len(EValueAll)):
        a = EValueAll[i]
        for j in range(0, len(a)):
            b = a[j]
            if ',' in b:
                for k in range(0, len(ETimeAll)):
                    c = ETimeAll[k]
                    for l in range(0, len(c)):
                        d = c[l]
                        s = d[1:len(d) - 1]
                        st1 = s.split(', ')
                        st2 = b.split(',')
                        if st1[0] == st2[0] and st1[1] == st2[1] and st1[2] == st2[2]:
                            hb = [ENameAll[k][l], ENameAll[i][j]]
                            setHb.append(hb)

    # AP = "pqrst"

    variablesSMT = []
    splitSMTFormula = smtFormula[9:].split(" AND ( TRUE, ")
    varCount = 1
    for i in smtFormula.split():
        # print(i)
        j = i.find(".f(")
        if j > 0:
            varCount = varCount + 1
    for i in range(varCount):
        variablesSMT.append("i_" + str(i))
    print("Variables: ")
    print(variablesSMT)
    strFormula = "Or(False"
    for word in splitSMTFormula[1:]:
        print(word)
        smtWord = createSMT(word, variablesSMT, AP)
        print(smtWord)
        strFormula = strFormula + ", And(True" + smtWord + " )"
    strFormula = strFormula + ")"
    print(strFormula)

    file = open(writeFile, "w")
    file.write("from z3.z3 import *\n")
    file.write("import time\n")
    file.write("\n")
    file.write("def unintFuncTestFive():\n")
    file.write("\n\n")
    file.write("\ts = Solver()\n")

    file.write("\n")
    file.write("\teps = " + str(eps) + "\n")
    file.write("\tnumEvent = " + str(len(setEvent)) + "\n")

    file.write("\tpowSet = [BitVecVal(0, " + str(len(setEvent)) + ")")
    for i in range(1, pow(2, len(setEvent))):
        file.write(", BitVecVal(" + str(i) + ", " + str(len(setEvent)) + ")")
    file.write("]\n")

    file.write("\thbSet = [(" + str(setHb[0][0]) + ", " + str(setHb[0][1]) + ")")
    for i in setHb[1:]:
        file.write(", (" + str(i[0]) + ", " + str(i[1]) + ")")
    file.write("]\n")

    file.write("\tv1 = Int('v1')\n")
    file.write("\tv2 = Int('v2')\n")
    file.write("\n")
    # file.write("\ttimeMap = Function('timeMap', IntSort(), IntSort())\n")

    # for i in range(0, len(ETimeAll)):
    #     a = ETimeAll[i]
    #     for j in range(0, len(a)):
    #         t = a[j][1:len(a[j]) - 1].split(', ')
    #         file.write("\ts.add(timeMap(" + str(ENameAll[i][j]) + ") == " + str(t[0]) + ")\n")

    file.write("\tvalMap = Function('valMap', IntSort(), BitVecSort(2))\n")

    for i in range(0, len(ETimeAll)):
        a = EValueAll[i]
        for j in range(0, len(a)):
            num = 0
            for s in AP:
                if s in a[j]:
                    num = (num << 1) + 1
                else:
                    num = num << 1
            file.write("\ts.add(valMap(" + str(ENameAll[i][j]) + ") == BitVecVal(" + str(num) + ", 2))\n")

    file.write("\teventList = {}\n")

    file.write("\tfor i in range(len(powSet)):\n")
    file.write("\t\teventList[i] = BitVec('eventList %i' % i, " + str(len(setEvent)) + ")\n")
    file.write("\t\ts.add(eventList[i] == powSet[i])\n")
    file.write("\n")
    file.write("\tf = Function('f', IntSort(), BitVecSort(" + str(len(setEvent)) + "))\n")
    file.write("\n")
    file.write("\tHappensBefore = Function('HappensBefore', IntSort(), IntSort(), BoolSort())\n")
    file.write("\n")
    file.write("\ts.add(And([HappensBefore(hbSet[i][0], hbSet[i][1]) for i in range(len(hbSet))]))\n")
    file.write("\n")
    file.write("\tx = Int('x')\n")
    file.write("\ty = Int('y')\n")
    file.write("\tz = Int('z')\n")
    file.write("\tk = Int('k')\n")
    file.write("\tn = Int('n')\n")
    file.write("\to = Int('o')\n")
    for i in variablesSMT:
        file.write("\t" + i + "= Int(\'" + i + "\')\n")
    file.write("\ts.add(x >= 0)\n")
    file.write("\ts.add(y >= 0)\n")
    file.write("\ts.add(z >= 0)\n")
    file.write("\ts.add(k >= 0)\n")
    file.write("\ts.add(n >= 0)\n")
    file.write("\ts.add(o >= 0)\n")
    for i in variablesSMT:
        file.write("\ts.add(" + i + " >= 0)\n")
    file.write("\ts.add(x <= len(eventList))\n")
    file.write("\ts.add(z <= len(eventList))\n")
    file.write("\ts.add(y > x)\n")
    file.write("\ts.add(z < x)\n")
    file.write("\ts.add(f(x) == eventList[len(eventList) - 1])\n")
    file.write("\ts.add(ForAll(y, Implies(y > x, f(y) == eventList[len(eventList) - 1])))\n")
    file.write("\ts.add(f(0) == eventList[0])\n")
    file.write("\ts.add(ForAll(k, Implies(And(k >= 0), Or([f(k) == eventList[i] for i in range(len(eventList))]))))\n")

    file.write("\ts.add(ForAll(z, Implies(And(z >= 0, z < x), ")
    for i in range(len(setEvent)):
        file.write("And(Implies(Not(Extract(" + str(i) + ", " + str(i) + ", f(z)) == Extract(" + str(i) + ", " + str(i) + ", f(z + 1))), ")
        if i == 0:
            file.write("And(Extract(" + str(len(setEvent) - 1) + ", 1, f(z)) == Extract(" + str(len(setEvent) - 1) + ", 1, f(z + 1)), Extract(0, 0, f(z)) == 0)), ")
        elif i == len(setEvent) - 1:
            file.write(
                "And(Extract(" + str(len(setEvent) - 2) + ", 0, f(z)) == Extract(" + str(len(setEvent) - 2) + ", 0, f(z + 1)), Extract(" + str(len(setEvent) - 1) + ", " +
                str(len(setEvent) - 1) + ", f(z)) == 0)), ")
        else:
            file.write("And(Extract(" + str(i - 1) + ", 0, f(z)) == Extract(" + str(i - 1) + ", 0, f(z + 1)), And(Extract(" + str(len(setEvent) - 1) + ", " + str(i + 1) + ", f(z)) == Extract(" +
                       str(len(setEvent) - 1) + ", " + str(i + 1) + ", f(z + 1)), Extract(" + str(i) + ", " + str(i) + ", f(z)) == 0))), ")
    file.write("And(Or([Not(Extract(i, i, f(z)) == Extract(i, i, f(z + 1))) for i in range(" + str(len(setEvent)) + ")]), True)")
    for i in range(len(setEvent)):
        file.write(")")
    file.write(")))\n")

    file.write("\ts.add(ForAll(n, And([Implies(And(HappensBefore(hbSet[i][0], hbSet[i][1]), Extract(hbSet[i][1] - 1, hbSet[i][1] - 1, f(x)) == 1), "
               "Extract(hbSet[i][0] - 1, hbSet[i][0] - 1, f(x)) == 1) for i in range(len(hbSet))])))\n")
    # print(formulaSMT)
    # file.write("\ts.add(Or(False, And(True, ")
    # for i in formulaSMT[2:]:
    #     for j in i:
    #         if j == "OR" or j == "FALSE" or j == "AND" or j == "TRUE" or j == '':
    #             continue
    #         file.write(j)
    #         if j != 'OR' and j != 'AND':
    #             file.write(", ")
    #         else:
    #             file.write("( ")
    #     file.write(")")
    # file.write(")\n")
    file.write("\n")
    file.write("\t" + strFormula + "\n")
    # file.write("\ts.add(" + strFormula + ")\n")

    file.write("\tresult = s.check()\n")
    file.write("\tprint(result)\n")
    file.write("\tif not (\"unsat\" in str(result)):\n")
    file.write("\t\tm = s.model()\n")
    file.write("\t\tprint(m)\n")
    file.write("\n")
    file.write("\n")
    file.write("def Z3abs(x):\n")
    file.write("\treturn If(x >= 0, x, -x)\n")
    file.write("\n")
    file.write("\n")
    file.write("if __name__ == \"__main__\":\n")
    file.write("\tstart = time.time()\n")
    file.write("\tunintFuncTestFive()\n")
    file.write("\tend = time.time()\n")
    file.write("\tprint(\"Time Taken : \" + str(end - start))\n")


if __name__ == "__main__":
    if len(sys.argv) == 7:
        eps = int(sys.argv[3])
        AP = sys.argv[5]
        main(sys.argv[1], sys.argv[2], sys.argv[4], int(sys.argv[6]))
    else:
        print("<traceFileName> <SMTfileName> <tsc-epsilon> <SMTFormula> <AP>")
