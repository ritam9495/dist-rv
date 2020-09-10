import sys
from itertools import combinations


def readFile(traceFile, procList):
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
            for i in procList:
                if str(i)+"_" in words[1]:
                    EName.append(name)
                    name = name + 1
                    EType.append(words[3])
                    EValue.append(words[5])
                    ETime.append(words[7])
                    break
    return ENameAll, ETimeAll, EValueAll, ETypeAll


def createSMT(formula, variables):
    formula = formula.strip()
    finalFormula = ""
    numBracket = 0
    if formula == "OR" or formula == "FALSE" or formula == "AND" or formula == "TRUE" or formula == '':
        return formula
    elif formula.find(".") != -1:
        first = formula.split(".")[0]
        second = formula.split(".")[1]
        if first[0] == "A":
            finalFormula = "ForAll("
        elif first[0] == "E":
            finalFormula = "Exists("
        var = ""
        for i in variables:
            if i in second:
                var = i
        finalFormula = finalFormula + var + ", "
        if len(first) > 4:
            xyz = first[1:].split()
            finalFormula = finalFormula + "Implies( And("
            numBracket = 1
            flag = 0
            for i in range(len(xyz)):
                if xyz[i] == "<=" or xyz[i] == "<" or xyz[i] == ">=" or xyz[i] == ">":
                    if flag == 0:
                        flag = 1
                    else:
                        finalFormula = finalFormula + ", "
                    finalFormula = finalFormula + xyz[i - 1] + " " + xyz[i] + " " + xyz[i + 1]
            finalFormula = finalFormula + "), "
    else:
        second = formula.replace("=", "==")
    try:
        xyz = second.split("=")
        num = 0
        if "||" in xyz[1]:
            flag = 0
            numBracket = numBracket + 1
            for i in xyz[1].split("||"):
                i = i.strip()
                print(i)
                if i == "<empty>":
                    num = 0
                else:
                    r = AP.find(i)
                    num = int(pow(2, r))
                if flag == 0:
                    flag = 1
                    finalFormula = finalFormula + "Or( " + "BV2Int(valMap(v1) | valMap(v2)) == " + str(num)
                else:
                    finalFormula = finalFormula + ", " + "BV2Int(valMap(v1) | valMap(v2)) == " + str(num)
        else:
            for i in xyz[1].split("&&"):
                i = i.strip()
                if i == "<empty>":
                    num = num | 0
                else:
                    r = AP.find(i)
                    num = num | int(pow(2, r))
            finalFormula = finalFormula + "And(True, BV2Int(valMap(v1) | valMap(v2)) == " + str(num) + ")"
        if second.strip()[0] == "f":
            finalFormula = finalFormula + ")" + ")" * numBracket
        else:
            finalFormula = second.strip()
    except IndexError:
        print("Error")
        pass
    return finalFormula


def main(traceFile, writeFile, smtFormula):
    file = open(writeFile, "w")

    file.write("from z3 import *\n")
    file.write("import time\n")
    file.write("\n")
    file.write("def unintFuncTestFive():\n")
    file.write("\ts = Solver()\n")

    file.write("\teps = " + str(eps) + "\n")

    procListNum = 0
    for procList in procListMain:
        procListNum = procListNum + 1
        ENameAll, ETimeAll, EValueAll, ETypeAll = readFile(traceFile, procList)
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
                        for l1 in range(0, len(c)):
                            d = c[l1]
                            s = d[1:len(d) - 1]
                            st1 = s.split(', ')
                            st2 = b.split(',')
                            if st1[0] == st2[0] and st1[1] == st2[1] and st1[2] == st2[2]:
                                hb = [ENameAll[k][l1], ENameAll[i][j]]
                                setHb.append(hb)
        variablesSMT = []
        formulaSMT = []
        splitSMTFormula = smtFormula.split()
        a = splitSMTFormula[-5].find("_")
        maxVariable = int(splitSMTFormula[-5][a + 1:])
        for i in range(maxVariable + 1):
            variablesSMT.append("i_" + str(i))
        formula = []
        strFormula = ""
        for word in smtFormula.split():
            if word == ')':
                strFormula = createSMT(strFormula, variablesSMT)
                formula.append(strFormula)
                strFormula = ""
                formulaSMT.append(formula)
                formula = []
            elif word == '(':
                strFormula = createSMT(strFormula, variablesSMT)
                formula.append(strFormula)
                strFormula = ""
                formulaSMT.append(formula)
                formula = []
            elif "," in word:
                if len(word) != 1:
                    strFormula = strFormula + " " + word[:len(word) - 1]
                strFormula = createSMT(strFormula, variablesSMT)
                formula.append(strFormula)
                strFormula = ""
            else:
                strFormula = strFormula + " " + word
        # print(formulaSMT)

        file.write("\tnumEvent" + str(procListNum) + " = " + str(len(setEvent)) + "\n")

        file.write("\tpowSet" + str(procListNum) + " = [BitVecVal(0, " + str(len(setEvent)) + ")")
        for i in range(1, pow(2, len(setEvent))):
            file.write(", BitVecVal(" + str(i) + ", " + str(len(setEvent)) + ")")
        file.write("]\n")

        file.write("\thbSet" + str(procListNum) + " = [(" + str(setHb[0][0]) + ", " + str(setHb[0][1]) + ")")
        for i in setHb[1:]:
            file.write(", (" + str(i[0]) + ", " + str(i[1]) + ")")
        file.write("]\n")

        file.write("\tv" + str(procListNum) + "1 = Int('v1')\n")
        file.write("\tv" + str(procListNum) + "2 = Int('v2')\n")
        file.write("\n")
        # file.write("\ttimeMap = Function('timeMap', IntSort(), IntSort())\n")

        # for i in range(0, len(ETimeAll)):
        #     a = ETimeAll[i]
        #     for j in range(0, len(a)):
        #         t = a[j][1:len(a[j]) - 1].split(', ')
        #         file.write("\ts.add(timeMap(" + str(ENameAll[i][j]) + ") == " + str(t[0]) + ")\n")

        file.write("\tvalMap" + str(procListNum) + " = Function('valMap" + str(procListNum) + "', IntSort(), BitVecSort(2))\n")

        for i in range(0, len(ETimeAll)):
            a = EValueAll[i]
            for j in range(0, len(a)):
                num = 0
                for s in "ab":
                    if s in a[j]:
                        num = (num << 1) + 1
                    else:
                        num = num << 1
                file.write("\ts.add(valMap" + str(procListNum) + "(" + str(ENameAll[i][j]) + ") == BitVecVal(" + str(num) + ", 2))\n")

        file.write("\teventList" + str(procListNum) + " = {}\n")

        file.write("\tfor i in range(len(powSet" + str(procListNum) + ")):\n")
        file.write("\t\teventList" + str(procListNum) + "[i] = BitVec('eventList %i' % i, " + str(len(setEvent)) + ")\n")
        file.write("\t\ts.add(eventList" + str(procListNum) + "[i] == powSet" + str(procListNum) + "[i])\n")
        file.write("\n")
        file.write("\tf" + str(procListNum) + " = Function('f" + str(procListNum) + "', IntSort(), BitVecSort(" + str(len(setEvent)) + "))\n")
        file.write("\n")
        file.write("\tHappensBefore" + str(procListNum) + " = Function('HappensBefore', IntSort(), IntSort(), BoolSort())\n")
        file.write("\n")
        file.write("\ts.add(And([HappensBefore" + str(procListNum) + "(hbSet" + str(procListNum) + "[i][0], hbSet" + str(procListNum) + "[i][1]) for i in range(len(hbSet" + str(procListNum) + "))]))\n")
        file.write("\n")
        file.write("\tx" + str(procListNum) + " = Int('x" + str(procListNum) + "')\n")
        file.write("\ty" + str(procListNum) + " = Int('y" + str(procListNum) + "')\n")
        file.write("\tz" + str(procListNum) + " = Int('z" + str(procListNum) + "')\n")
        file.write("\tk" + str(procListNum) + " = Int('k" + str(procListNum) + "')\n")
        file.write("\tn" + str(procListNum) + " = Int('n" + str(procListNum) + "')\n")
        file.write("\to" + str(procListNum) + " = Int('o" + str(procListNum) + "')\n")
        for i in variablesSMT:
            file.write("\t" + i + str(procListNum) + "= Int(\'" + i + "\')\n")
        file.write("\ts.add(x" + str(procListNum) + " >= 0)\n")
        file.write("\ts.add(y" + str(procListNum) + " >= 0)\n")
        file.write("\ts.add(z" + str(procListNum) + " >= 0)\n")
        file.write("\ts.add(k" + str(procListNum) + " >= 0)\n")
        file.write("\ts.add(n" + str(procListNum) + " >= 0)\n")
        file.write("\ts.add(o" + str(procListNum) + " >= 0)\n")
        for i in variablesSMT:
            file.write("\ts.add(" + i + str(procListNum) + " >= 0)\n")
        file.write("\ts.add(x" + str(procListNum) + " <= len(eventList" + str(procListNum) + "))\n")
        file.write("\ts.add(z" + str(procListNum) + " <= len(eventList" + str(procListNum) + "))\n")
        file.write("\ts.add(y" + str(procListNum) + " > x" + str(procListNum) + ")\n")
        file.write("\ts.add(z" + str(procListNum) + " < x" + str(procListNum) + ")\n")
        file.write("\ts.add(f" + str(procListNum) + "(x" + str(procListNum) + ") == eventList" + str(procListNum) + "[len(eventList" + str(procListNum) + ") - 1])\n")
        file.write("\ts.add(ForAll(y" + str(procListNum) + ", Implies(y" + str(procListNum) + " > x" + str(procListNum) + ", f" + str(procListNum) + "(y" + str(procListNum) +
                   ") == eventList" + str(procListNum) + "[len(eventList" + str(procListNum) + ") - 1])))\n")
        file.write("\ts.add(f" + str(procListNum) + "(0) == eventList" + str(procListNum) + "[0])\n")
        file.write("\ts.add(ForAll(k" + str(procListNum) + ", Implies(And(k" + str(procListNum) + " >= 0), Or([f" + str(procListNum) + "(k" + str(procListNum) + ") == eventList" + str(procListNum) +
                   "[i] for i in range(len(eventList" + str(procListNum) + "))]))))\n")

        file.write("\ts.add(ForAll(z" + str(procListNum) + ", Implies(And(z" + str(procListNum) + " >= 0, z" + str(procListNum) + " < x" + str(procListNum) + "), ")
        for i in range(len(setEvent)):
            file.write("And(Implies(Not(Extract(" + str(i) + ", " + str(i) + ", f" + str(procListNum) + "(z" + str(procListNum) + ")) == Extract(" + str(i) + ", " + str(i) + ", f" + str(procListNum) + "(z" + str(procListNum) + " + 1))), ")
            if i == 0:
                file.write("And(Extract(" + str(len(setEvent) - 1) + ", 1, f" + str(procListNum) + "(z" + str(procListNum) + ")) == Extract(" + str(len(setEvent) - 1) + ", 1, f" + str(procListNum) +
                           "(z" + str(procListNum) + " + 1)), Extract(0, 0, f" + str(procListNum) + "(z" + str(procListNum) + ")) == 0)), ")
            elif i == len(setEvent) - 1:
                file.write(
                    "And(Extract(" + str(len(setEvent) - 2) + ", 0, f" + str(procListNum) + "(z" + str(procListNum) + ")) == Extract(" + str(len(setEvent) - 2) + ", 0, f" + str(procListNum) + "(z" +
                    str(procListNum) + " + 1)), Extract(" + str(len(setEvent) - 1) + ", " + str(len(setEvent) - 1) + ", f" + str(procListNum) + "(z" + str(procListNum) + ")) == 0)), ")
            else:
                file.write("And(Extract(" + str(i - 1) + ", 0, f" + str(procListNum) + "(z" + str(procListNum) + ")) == Extract(" + str(i - 1) + ", 0, f" + str(procListNum) + "(z" + str(procListNum) +
                           " + 1)), And(Extract(" + str(len(setEvent) - 1) + ", " + str(i + 1) + ", f" + str(procListNum) + "(z" + str(procListNum) + ")) == Extract(" + str(len(setEvent) - 1) + ", " +
                           str(i + 1) + ", f" + str(procListNum) + "(z" + str(procListNum) + " + 1)), Extract(" + str(i) + ", " + str(i) + ", f" + str(procListNum) + "(z" + str(procListNum) + ")) == 0))), ")
        file.write("And(Or([Not(Extract(i, i, f" + str(procListNum) + "(z" + str(procListNum) + ")) == Extract(i, i, f" + str(procListNum) + "(z" + str(procListNum) + " + 1))) for i in range(" + str(len(setEvent)) + ")]), True)")
        for i in range(len(setEvent)):
            file.write(")")
        file.write(")))\n")

        file.write("\ts.add(ForAll(n" + str(procListNum) + ", And([Implies(And(HappensBefore" + str(procListNum) + "(hbSet" + str(procListNum) + "[i][0], hbSet" + str(procListNum) +
                   "[i][1]), Extract(hbSet" + str(procListNum) + "[i][1] - 1, hbSet" + str(procListNum) + "[i][1] - 1, f" + str(procListNum) + "(x" + str(procListNum) + ")) == 1), "
                   "Extract(hbSet" + str(procListNum) + "[i][0] - 1, hbSet" + str(procListNum) + "[i][0] - 1, f" + str(procListNum) + "(x" + str(procListNum) + ")) == 1) for i in range(len(hbSet" +
                   str(procListNum) + "))])))\n")
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

    file.write("\ts.add(Or( False, And( True, ")
    for i in range(len(procListMain)):
        binNum = 0
        for j in procListMain[i]:
            binNum = binNum + int(pow(2, 5 - j))
        file.write("Exists(i_0" + str(i + 1) + ", valMap" + str(i + 1) + "(v" + str(i + 1) + "1) | valMap1(v" + str(i + 1) + "2) != " + str(binNum) + "), ForAll(i_1" + str(i + 1) + ", And( i_2"
                   + str(i + 1) + " <= i_1" + str(i + 1) + ", i_1" + str(i + 1) + " < i_0" + str(i + 1) + ", valMap" + str(i + 1) + "(v" + str(i + 1) + "1) | valMap1(v" + str(i + 1) + "2) == "
                   + str(binNum) + ")), i_2" + str(i + 1) + " == 0, ")
    file.write(")))\n")

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
    file.write("\tprint(\"Time Taken : \" + str(end - start))")


if __name__ == "__main__":
    if len(sys.argv) == 8:
        eps = int(sys.argv[3])
        AP = sys.argv[5]
        numProcess = int(sys.argv[7])
        procListMain = list(combinations(list(range(1, numProcess + 1)), 3))
        # for i in range(numProcess - 1):
        #     # procListMain.append([i + 1, i + 2, i + 3])
        #     procListMain.append([i + 1, i + 2])
        # if numProcess != 2:
        #     # procListMain.append([numProcess - 1, numProcess, 1])
        #     # procListMain.append([numProcess, 1, 2])
        #     procListMain.append([numProcess, 1])
        print(procListMain)
        main(sys.argv[1], sys.argv[2], sys.argv[4])
    elif len(sys.argv) == 7:
        eps = int(sys.argv[3])
        AP = sys.argv[5]
        numProcess = int(sys.argv[6])
        procListMain = list(combinations(list(range(1, numProcess + 1)), 3))
        main(sys.argv[1], sys.argv[2], sys.argv[4])
    else:
        print("<traceFileName> <SMTfileName> <tsc-epsilon> <SMTFormula> <AP>")