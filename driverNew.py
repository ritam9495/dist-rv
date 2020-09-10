'''
Created on Feb 16, 2020

@author: Anik
'''

import re
import time

from z3 import *

pathToGraphDir = ""
stateMapper = {}

stateSet = []

stateStart = []
stateAccept = []
stateReject = []

paths = []

sAcc = Solver()
sRej = Solver()


def labelOf(stateFrom, stateTo):

    # print(stateFrom, stateTo)

    for state in stateMapper[stateTo]:

        print(stateMapper[stateTo])
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

        print(path[0], path[1])

        # AND; to bind all constraints in a path
        text += ", AND ( TRUE"

        # Terminating (Accept/Reject) constraint
        text += ", Ei_{}.f(i_{}) = ".format(count, count) + labelOf(path[1], path[0])
        count += 1

        # SMT section start
        f = Function('f', IntSort(), BoolSort())

        indexInPath = 0
        qtInPath = []
        conInPath = []

        # qt = Int('qt')
        qtInPath.append(Int('qt{}_{}'.format(indexparent, indexInPath)))

        conInPath.append(f(qtInPath[indexInPath]) == And(((len(a) / pow(10, (len(a) - qtInPath[indexInPath]))) % 10) == 1, ((len(b) / pow(10, (len(a) - qtInPath[indexInPath]))) % 10) == 1))

        indexInPath += 1
        # SMT section end

        # Remaining constraints; in bottom-up order
        for i in range(1, len(path)):

            # Check for loop
            if labelOf(path[i], path[i]) != "NONE":

                text += " , Ai_{} <= i_{} < i_{}.f(i_{}) = ".format(count + 1, count, count - 1, count) + labelOf(path[i], path[i])
                count += 1

                # SMT section start
                qtInPath.append(Int('qt{}_{}'.format(indexparent, indexInPath)))
                qtInPath.append(Int('qt{}_{}'.format(indexparent, indexInPath + 1)))  # Should probably be contingent upon a condition

                conInPath.append(ForAll(qtInPath[indexInPath], Implies(And(qtInPath[indexInPath] < qtInPath[indexInPath - 1], qtInPath[indexInPath] >= qtInPath[indexInPath + 1]), Or(False, f(qtInPath[indexInPath]) == And(((len(a) / pow(10, (len(a) - qtInPath[indexInPath]))) % 10) == 1, ((len(b) / pow(10, (len(a) - qtInPath[indexInPath]))) % 10) == 1)))))
                # conInPath.append(f(qtInPath[indexInPath]) == And(((len(a) / pow(10, (len(a) - qtInPath[indexInPath]))) % 10) == 1, ((len(b) / pow(10, (len(a) - qtInPath[indexInPath]))) % 10) == 1))

                indexInPath += 1
                # SMT section end

            # Check if next state exists
            if i + 1 < len(path):

                text += " , Ei_{} = i_{}-1.f(i_{}) = ".format(count, count - 1, count) + labelOf(path[i + 1], path[i])
                count += 1

                # SMT section start
                qtInPath.append(Int('qt{}_{}'.format(indexparent, indexInPath)))

                conInPath.append(And(qtInPath[indexInPath] == qtInPath[indexInPath] - 1, f(qtInPath[indexInPath]) == And(((len(a) / pow(10, (len(a) - qtInPath[indexInPath]))) % 10) == 1, ((len(b) / pow(10, (len(a) - qtInPath[indexInPath]))) % 10) == 1)))

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

    while(startStatefound == False):

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

    stateStart.append(stateStartTemp)

    # print(stateStart[0], stateSet, stateStartTemp)


def populateMapper(lines):

    # print(stateMapper)

    for line in lines:

        stateFrom, stateTo, isLoop = getStates(line)
        stateLabel = getLabel(line)

        newEntry = True

        # print(stateTo, stateFrom, line)

        if (stateFrom != None or  stateTo != None or stateLabel != None):

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


def main():

    formulaFile = fileName

    ltl3 = getLTL3(formulaFile)
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
    listStates = []
    initState = None
    acceptState = None
    rejectState = None
    for line in open(formulaFile, "r"):
        if "style=filled" in line:
            a = line.find("\"")
            b = line.find("\"", a + 1)
            state = line[a:b + 1]
            listStates.append(state[2:-2])
            if "(0, 0)" in line:
                initState = state[2:-2]
            elif "(-1, 1)" in line:
                rejectState = state[2:-2]
            elif "(1, -1)" in line:
                acceptState = state[2:-2]
    # print(acceptState)
    print("Full:")
    print(stateMapper, "\n")
    print("Partial:")
    # print(stateMapper["1, -1"])
    print(stateMapper[initState])
    if rejectState is not None:
        print(stateMapper[rejectState], "\n")
        printAllPaths(rejectState, initState)
    else:
        print(stateMapper[acceptState], "\n")
        printAllPaths(acceptState, initState)
    # printAllPaths("1, -1", "0, 0")

    # Reverse state order
    # for path in paths:

        # path.reverse()

    # print(paths)

    print(LTL3_to_SMT_text())


if __name__ == '__main__':

    start = time.time()
    fileName = sys.argv[1]
    main()

    print("Terminated..")
    print("Time elapsed :", (time.time() - start), "seconds")

    pass
