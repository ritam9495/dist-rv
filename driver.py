'''
Created on Feb 16, 2020

@author: Anik
'''

import re
import time

from z3 import *

pathToGraphDir = "digraphs/"
stateMapper = {}

stateSet = []

stateStart = []
stateAccept = []
stateReject = []

paths = []

sAcc = Solver()
sRej = Solver()


def labelOf(stateFrom, stateTo):
    print(stateFrom, stateTo)

    for state in stateMapper[stateTo]:

        # print(stateMapper[stateTo])
        print(state)

        if (len(state) == 2) & (state[0] == stateFrom):
            return state[1]

    return "NONE"


def LTL3_to_SMT_text():
    # Test input
    a = "111111111"
    b = "111111111"

    text = ""
    count = 0

    # OR; to bind constraints for different paths
    text += "OR ( FALSE"

    # SMT section start
    indexparent = 0

    constraintPaths = []
    constraintQuantifiers = []
    # constraintAllPaths = Or(False, True)

    for path in paths:

        # AND; to bind all constraints in a path
        text += ", AND ( TRUE"

        # Terminating (Accept/Reject) constraint
        text += ", Ei_{}.f(i_{}) = ".format(count, count) + labelOf(path[0], path[1])
        count += 1

        # SMT section start
        f = Function('f', IntSort(), BoolSort())

        indexInPath = 0
        qtInPath = []
        conInPath = []

        # qt = Int('qt')
        qtInPath.append(Int('qt{}_{}'.format(indexparent, indexInPath)))

        conInPath.append(
            f(qtInPath[indexInPath]) == And(((len(a) / pow(10, (len(a) - qtInPath[indexInPath]))) % 10) == 1,
                                            ((len(b) / pow(10, (len(a) - qtInPath[indexInPath]))) % 10) == 1))

        indexInPath += 1
        # SMT section end

        # Remaining constraints; in bottom-up order
        for i in range(1, len(path)):

            # Check for loop
            if labelOf(path[i], path[i]) != "NONE":
                text += " , Ai_{} <= i_{} < i_{}.f(i_{}) = ".format(count + 1, count, count - 1, count) + labelOf(
                    path[i], path[i])
                count += 1

                # SMT section start
                qtInPath.append(Int('qt{}_{}'.format(indexparent, indexInPath)))
                qtInPath.append(Int(
                    'qt{}_{}'.format(indexparent, indexInPath + 1)))  # Should probably be contingent upon a condition

                conInPath.append(ForAll(qtInPath[indexInPath], Implies(
                    And(qtInPath[indexInPath] < qtInPath[indexInPath - 1],
                        qtInPath[indexInPath] >= qtInPath[indexInPath + 1]), Or(False, f(qtInPath[indexInPath]) == And(
                        ((len(a) / pow(10, (len(a) - qtInPath[indexInPath]))) % 10) == 1,
                        ((len(b) / pow(10, (len(a) - qtInPath[indexInPath]))) % 10) == 1)))))
                # conInPath.append(f(qtInPath[indexInPath]) == And(((len(a) / pow(10, (len(a) - qtInPath[indexInPath]))) % 10) == 1, ((len(b) / pow(10, (len(a) - qtInPath[indexInPath]))) % 10) == 1))

                indexInPath += 1
                # SMT section end

            # Check if next state exists
            if i + 1 < len(path):
                text += " , Ei_{} = i_{}-1.f(i_{}) = ".format(count, count - 1, count) + labelOf(path[i], path[i + 1])
                count += 1

                # SMT section start
                qtInPath.append(Int('qt{}_{}'.format(indexparent, indexInPath)))

                conInPath.append(And(qtInPath[indexInPath] == qtInPath[indexInPath] - 1,
                                     f(qtInPath[indexInPath]) == And(
                                         ((len(a) / pow(10, (len(a) - qtInPath[indexInPath]))) % 10) == 1,
                                         ((len(b) / pow(10, (len(a) - qtInPath[indexInPath]))) % 10) == 1)))

        # count -= 1
        text += ", i_{} = 0 )".format(count)

    text += " )"

    # UPDATE SOLVER HERE

    return text


def printAllPathsUtil(u, d, visited, path):
    # Mark the current node as visited and store in path
    visited[u] = True
    path.append(u)

    # If current vertex is same as destination, then print 
    # current path[] 
    if u == d:

        # print(path)
        paths.append(path.copy())

    else:

        print(stateMapper[u])
        # If current vertex is not destination 
        # Recur for all the vertices adjacent to this vertex 
        for i in range(1, len(stateMapper[u])):

            if visited[stateMapper[u][i][0]] == False:
                printAllPathsUtil(stateMapper[u][i][0], d, visited, path)

    # Remove current vertex from path[] and mark it as unvisited 
    path.pop()
    visited[u] = False


def printAllPaths(s, d):
    # Mark all the vertices as not visited 
    # visited = [False] * (V)

    # visited = [False] * len(stateSet)

    visited = {}

    for state in stateSet:
        visited[state] = False

    # Create an array to store paths 
    path = []

    # Call the recursive helper function to print all paths 
    printAllPathsUtil(s, d, visited, path)


def mergeLabels():  # Obsolete

    for state in stateSet:

        # print(state)
        print(stateMapper[state])

        for i in range(1, len(stateMapper[state]) - 2):

            print("i", i)

            for j in range(i + 1, len(stateMapper[state]) - 1):

                print("j", j)

                if stateMapper[state][i][0] == stateMapper[state][j][0]:
                    stateMapper[state][i][1] += " OR " + stateMapper[state][j][1]
                    stateMapper[state].pop(j)


def markStartState2():  # Obsolete

    # print(stateMapper)

    # backtrack from accept state
    startStateFromAcc = stateAccept[0]
    startStateFromAcc = "1, -1"

    # print(stateMapper[startStateFromAcc])
    tmp = "x"

    startStatefound = False

    while (startStatefound == False):

        startStatefound = True

        for state in stateMapper[startStateFromAcc]:
            # print(stateMapper[startStateFromAcc])

            if (state[0] != startStateFromAcc) & (len(state) == 2):
                tmp = state[0]
                print(state)
                startStateFromAcc = tmp
                startStatefound = False
                break

        # tmp = startStateFromAcc
        print(tmp)


def markStartState():
    stateStartTemp = stateSet.copy()

    for stateTo in stateSet:

        for stateFrom in stateMapper[stateTo]:

            if (len(stateFrom) == 2) & (stateFrom[0] != stateTo):
                stateStartTemp.remove(stateTo)
                break

    if len(stateStartTemp) != 1:
        print("Error : Multiple start states detected")

    stateStart.append(stateStartTemp[0])

    # print(stateStart[0], stateSet, stateStartTemp)


def populateMapper(lines):
    # print(stateMapper)

    for line in lines:

        stateFrom, stateTo, isLoop = getStates(line)
        stateLabel = getLabel(line)

        newEntry = True

        # print(stateTo, stateFrom, line)

        if (stateFrom != None or stateTo != None or stateLabel != None):

            # stateMapper[stateFrom] = []
            for state in stateMapper[stateTo]:

                if (len(state) == 2) & (state[0] == stateFrom):
                    state[1] += "||" + stateLabel
                    newEntry = False

            if newEntry:
                stateMapper[stateTo].append([stateFrom, stateLabel])

    # print(stateMapper)

    markStartState()


def createStatesInMapper(lines):
    for line in lines:

        if ")\", style=filled, color=" in line:

            try:

                match = re.compile("\"\(.*\)\" \[label=\"\(")
                label = match.findall(line)[0][2:-12]

                if "green" in line:
                    stateMapper[label] = [["accept"]]
                    stateAccept.append(label)

                if "red" in line:
                    stateMapper[label] = [["reject"]]
                    stateReject.append(label)

                if "yellow" in line:
                    stateMapper[label] = [["unknown"]]

                stateSet.append(label)

            except:

                # print("Given line :", line, "could not be parsed.")
                pass


def getStates(line):
    # print(line)

    try:

        match = re.compile("\(.*\)\" -> \"\(")
        stateFrom = match.findall(line)[0][1:-8]

        match = re.compile("\)\" -> \"\(.*\)\" \[label = \"\(")
        stateTo = match.findall(line)[0][8:-14]

        # print(stateFrom, stateTo)

        return stateFrom, stateTo, stateTo == stateFrom

    except:

        # print("Given line :", line, "could not be parsed.")
        return None, None, False


def getLabel(line):
    # print(line)

    try:

        match = re.compile("\)\" \[label = \"\(.*\)\"\]")
        label = match.findall(line)[0][14:-3]

        return label

    except:

        # print("Given line :", line, "could not be parsed.")
        return None


def getLTL3(fileName):
    ltl3 = []
    path = pathToGraphDir + fileName

    file = open(path)

    line = file.readline()

    while line:
        line = file.readline()
        ltl3.append(line.rstrip())

    file.close()

    return ltl3


def unIntFuncTestFour():
    # Initialize solver
    s = Solver()
    eps = 2

    # powSet = [0, 1, 2, 12, 3, 13, 23, 123, 4, 14, 24, 124, 34, 134, 234, 1234]
    eventCount = 4
    powSet = [0, 11000, 10200, 21200, 10030, 21030, 20230, 31230, 10004, 21004, 20204, 31204, 20034, 31034, 30234,
              41234]
    hbSet = [(1, 2), (3, 4), (1, 4)]
    t1 = Int('t1')
    t2 = Int('t2')
    timeMap = Function('map', IntSort(), IntSort())
    s.add(timeMap(1) == 1)
    s.add(timeMap(2) == 2)
    s.add(timeMap(3) == 1)
    s.add(timeMap(4) == 2)

    listEvent = {}

    for i in range(len(powSet)):
        listEvent[i] = Int('listEvent %i' % i)
        s.add(listEvent[i] == powSet[i])

    # Uninterpreted Function
    f = Function('f', IntSort(), IntSort())

    InCut = Function('InCut', IntSort(), BoolSort())
    HappensBefore = Function('HappensBefore', IntSort(), IntSort(), BoolSort())

    s.add(And([HappensBefore(hbSet[i][0], hbSet[i][1]) for i in range(len(hbSet))]))

    e1 = Int('e1')
    e2 = Int('e2')

    # Initialize x
    x = Int('x')
    y = Int('y')
    z = Int('z')

    k = Int('k')
    n = Int('n')
    o = Int('o')

    # x, y, z are non-negative natural numbers
    s.add(x >= 0)
    s.add(y >= 0)
    s.add(z >= 0)
    s.add(k >= 0)
    s.add(n >= 0)
    s.add(o >= 0)

    # x and z cannot be greater than the cardinality of the power set of events
    s.add(x <= len(listEvent))
    s.add(z <= len(listEvent))

    s.add(y > x)
    s.add(z < x)

    s.add(f(x) == listEvent[len(listEvent) - 1])

    s.add(ForAll(y, Implies(y > x, f(y) == listEvent[len(listEvent) - 1])))

    s.add(f(0) == listEvent[0])

    # Restrict domain and range
    s.add(ForAll(k, Implies(And(k >= 0), Or([f(k) == listEvent[i] for i in range(len(listEvent))]))))

    s.add(ForAll(z, Implies(And(z >= 0, z < x),
                            And(((f(z) / pow(10, eventCount)) + 1) == (f(z + 1) / pow(10, eventCount)), True))))

    e1 = Int('e1')
    e2 = Int('e2')
    e3 = Int('e3')

    s.add(ForAll(n, And([Implies(And(HappensBefore(hbSet[i][0], hbSet[i][1]),
                                     (f(n) % pow(10, (eventCount + 1) - hbSet[i][1])) / pow(10, (
                                             eventCount - hbSet[i][1])) == hbSet[i][1], n >= 1, n < x),
                                 (f(n) % pow(10, (eventCount + 1) - hbSet[i][0])) / pow(10,
                                                                                        (eventCount - hbSet[i][0])) ==
                                 hbSet[i][0]) for i in range(len(hbSet))])))

    s.add(ForAll([n], And([Implies(
        And(Not(((f(n) % pow(10, (eventCount + 1) - (i + 1))) / pow(10, (eventCount - (i + 1)))) == 0), n >= 1, n < x),
        ((f(n) % pow(10, (eventCount + 1) - (i + 1))) / pow(10, (eventCount - (i + 1)))) == (
                (f(n + 1) % pow(10, (eventCount + 1) - (i + 1))) / pow(10, (eventCount - (i + 1))))) for i in
        range(eventCount)])))

    # HLC
    s.add(ForAll([t1, t2], (
        Implies(And(t1 >= 0, t1 <= eventCount, t2 >= 0, t2 <= eventCount), Z3abs(timeMap(t1) - timeMap(t2)) <= eps))))

    # Satisfiability checking
    print(s.check())

    # Modeling
    m = s.model()
    print(m)


def Z3abs(x):
    return If(x >= 0, x, -x)


def main(fileName, startState, endState):
    testFile = fileName

    ltl3 = getLTL3(testFile)
    # print(populateMapper(ltl3[0]))

    createStatesInMapper(ltl3)
    populateMapper(ltl3)
    # mergeLabels()

    # print(createStatesInMapper(ltl3))

    #     mapper = {}
    #     s = []
    #     s.append("aj")
    #
    #     mapper["anik"] = []
    #     mapper["anik"].append("ax")
    #     mapper["anik"].append("ab")

    # print("Full:")
    # print(stateMapper, "\n")
    # print("Partial:")
    # print(stateMapper["1, -1"])

    # print(stateMapper["0, 0"])
    # print(stateMapper["1, 1"])
    # print(stateMapper["-1, 1"], "\n")

    printAllPaths(endState, startState)

    # Reverse state order
    # for path in paths:
    #     path.reverse()
    #
    # print(paths)
    print("LTL SPEC")
    print(LTL3_to_SMT_text())


if __name__ == '__main__':
    if len(sys.argv) == 4:
        start = time.time()

        main(sys.argv[1], sys.argv[2], sys.argv[3])

        print("Terminated..")
        print("Time elapsed :", (time.time() - start), "seconds")

    pass
