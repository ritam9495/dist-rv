import subprocess
import sys
import time
from scipy.stats import sem, t
from numpy import mean

import xlsxwriter as xlsxwriter


def createTraceFile(traceFile, traceSliceFile, start, end, eps):
    file1 = open(traceFile, "r")
    file2 = open(traceSliceFile, "w")
    start = min(start, abs(start - eps))

    for line in file1:
        words = line.split("\"")
        if "Process" in words[0]:
            file2.write(line)
        elif "Event" in words[0]:
            time = words[7].split(", ")
            if start <= int(time[0][1:]) <= end:
                file2.write(line)
    file1.close()
    file2.close()


def main1():
    # numIterMain = 6
    workbook = xlsxwriter.Workbook("report_" + str(0) + ".xlsx")
    worksheet = workbook.add_worksheet()
    worksheet.write(0, 0, "Segment num")
    worksheet.write(0, 1, "numProcess")
    worksheet.write(0, 2, "epsilon")
    worksheet.write(0, 3, "Computation Length")
    worksheet.write(0, 4, "Event Rate")
    worksheet.write(0, 5, "Mean Runtime")
    worksheet.write(0, 6, "Conf. Int.")
    for fileNum in [0]:
        row = 1
        for numProcess in [2]:
            segmentCount = [20]
            # numProcess = 3
            numIter = 1
            # for eventRate in [10, 12, 15]:
            eventRate = 1
            # for msgRate in [1, 2, 4, 6]:
            msgRate = 1
            for numSegment in [10, 15, 20, 25, 30, 35, 40]:
                # numSegment = 21
                # for compLength in [200]:
                for compLength in [200, 300, 400, 500, 600, 800]:
                    eps = 25
                    # compLength = 500
                    runtime = [0] * numIter
                    traceFile = "trace" + str(numProcess) + "_" + str(int(compLength / 10)) + ".txt"
                    # print(traceFile)

                    for tryNum in range(numIter):
                        output0 = subprocess.getstatusoutput("python synth-system.py " + str(numProcess) + " " + str(compLength) + " " + traceFile)
                        # print(output0[1])
                        runtime[tryNum] = runExp(fileNum, traceFile, eps, numSegment, compLength, numProcess)
                        print("compLength: " + str(compLength) + " eventRate: " + str(eventRate) + " numSegment: " + str(numSegment) + " msgRate: " + str(msgRate) + " numProcess: " + str(numProcess) + " epsilon: " + str(eps) + " formulaNum: " + str(fileNum) + " runtime: " + str(runtime[tryNum]))

                        sys.stdout.flush()

                    worksheet.write(row, 0, str(numSegment))
                    worksheet.write(row, 1, str(numProcess))
                    worksheet.write(row, 2, str(eps))
                    worksheet.write(row, 3, str(compLength))
                    worksheet.write(row, 4, str(eventRate))
                    mRuntime = mean(runtime)
                    stdErrRuntime = sem(runtime)
                    errRuntime = stdErrRuntime * t.ppf((1 + 0.95) / 2, numIter - 1)
                    print("Final Results")
                    print("Mean: " + str(mRuntime))
                    print("Std Dev: " + str(stdErrRuntime))
                    print("95% CI: " + str(errRuntime))
                    worksheet.write(row, 5, str(round(float(mRuntime), 3)))
                    worksheet.write(row, 6, str(round(errRuntime, 3)))
                    row = row + 1
        workbook.close()


def runExp(fileNum, traceFile, eps, numSegments, maxTime, numProcess):
    fileName = directory + str(fileNum) + ".txt"
    formulaFile = open(fileName, "r")
    listStates = []
    currentState = None
    finalAccept = None
    finalReject = None
    AP = ""
    for line in formulaFile:
        if "style=filled" in line:
            a = line.find("\"")
            b = line.find("\"", a + 1)
            state = line[a:b + 1]
            listStates.append(state)
            if "(0, 0)" in line:
                currentState = state
            elif "(-1, 1)" in line:
                finalReject = state
            elif "(1, -1)" in line:
                finalAccept = state
        if "->" in line:
            a = line.find("label")
            label = line[a + 9:-4]
            if label != "(<empty>)":
                for letter in label[1:-1]:
                    if letter != '&':
                        if letter not in AP:
                            AP = AP + letter

    # flag = 0
    # maxTime = 300
    steps = int(maxTime / numSegments)
    steps = numSegments
    start = - steps
    end = 0
    sumTime = 0
    startTime = 0
    totTime = 0
    while currentState != finalAccept and currentState != finalReject:
        # if flag == 0:
        start = start + steps
        end = end + steps
        # print(str(start) + " " + str(end))
        if end > maxTime:
            break
        #     if finalAccept is not None:
        #         checkState = finalAccept
        #     else:
        #         flag = 1 - flag
        #         continue
        # else:
        #     if finalReject is not None:
        #         checkState = finalReject
        #     else:
        #         flag = 1 - flag
        #         continue
        # output1 = subprocess.getstatusoutput("python3 driver.py formula.txt " + currentState + " " + checkState)
        output1 = subprocess.getstatusoutput("python driverNew.py " + str(fileName))
        # print(output1[1])
        x = output1[1].find("OR")
        y = output1[1].find("Terminated", x)
        smtFormula = output1[1][x:y - 1]
        # print(smtFormula)
        # print("Driver: Done!")
        createTraceFile(traceFile, "traceSlice.txt", start, end, eps)
        startTime = time.time()
        output2 = subprocess.getstatusoutput("python checker.py traceSlice.txt my_uninterpretedFunction.py " + str(eps) + " \"" + smtFormula + "\" \"" + AP + "\" " + str(fileNum))
        # print(output2[1])
        # print("Checker: Done!")
        output3 = subprocess.getstatusoutput("python my_uninterpretedFunction.py")
        # print(output3[1])
        try:
            a = str(output3[1]).rfind(":")
            # print(str(output3[1])[a + 2:-2])
            sumTime = sumTime + float(str(output3[1])[a + 2:-2])
            totTime = totTime + (time.time() - startTime)
        except ValueError:
            sumTime = sumTime
            totTime = totTime
        # flag = 1 - flag
        # elif "sat" in output3[1]:
        #     currentState = checkState
        #     print(output3[1])
    print("Total time: " + str(totTime))
    return sumTime


if __name__ == "__main__":
    directory = "formulaFiles/f"
    main1()
