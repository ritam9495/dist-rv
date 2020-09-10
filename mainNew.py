import subprocess
import sys
import time
from scipy.stats import sem, t
from numpy import mean
import multiprocessing
import math

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


def main(numMultiProcess):
    # numIterMain = 6
    row = 1
    workbook = xlsxwriter.Workbook("reportMulti_" + str(numMultiProcess) + ".xlsx")
    worksheet = workbook.add_worksheet()
    worksheet.write(0, 0, "SegmentLength")
    worksheet.write(0, 1, "numProcess")
    worksheet.write(0, 2, "epsilon")
    worksheet.write(0, 3, "Computation Length")
    worksheet.write(0, 4, "Event Rate")
    worksheet.write(0, 5, "Mean Runtime")
    worksheet.write(0, 6, "Conf. Int.")
    for fileNum in [0]:
        for compLength in [2000]:
            for numProcess in [15]:
                # segmentCount = [21]
                # segmentLength = 10
                # numProcess = 3
                # numIter = 10
                # for eventRate in [10, 12, 15]:
                eventRate = 10
                # eps = 15
                # for msgRate in [1, 2, 4, 6]:
                msgRate = 1
                for segmentLength in [10]:
                    for eps in [15]:
                        # numSegment = 21
                        traceFile = "trace" + str(numProcess) + "_" + str(int(compLength / 10)) + ".txt"
                        output0 = subprocess.getstatusoutput("python synth-system.py " + str(numProcess) + " " + str(compLength) + " " + traceFile)
                        # print(output0[1])
                        manager = multiprocessing.Manager()
                        return_dict = manager.dict()
                        listProcess = []
                        # for compLength in [200]:
                        segmentNum = 0
                        startTime = time.time()
                        # segmentLengthNew = compLength / multiprocessing.cpu_count()
                        # numMultiProcess = math.ceil(compLength/segmentLength)
                        segmentLengthNew = compLength / numMultiProcess
                        segmentStart = 0
                        segmentEnd = segmentLengthNew
                        while segmentStart != compLength:
                            segmentNum = segmentNum + 1
                            p = multiprocessing.Process(target=multi_process_func, args=(segmentNum, segmentStart, segmentEnd, segmentLength, fileNum, traceFile, eps,))
                            listProcess.append(p)
                            p.start()

                            segmentStart = segmentEnd
                            segmentEnd = min(compLength, segmentEnd + segmentLengthNew)

                            sys.stdout.flush()

                        for p in listProcess:
                            p.join()
                        finalTime = time.time() - startTime
                        print("Final TIME: " + str(finalTime))
                        runtime = 0.0
                        # for runtime_return in return_dict:
                        #     runtime = runtime + float(runtime_return)
                        print("compLength: " + str(compLength) + " eventRate: " + str(eventRate) + " segmentLength: " + str(segmentLength) +
                              " msgRate: " + str(msgRate) + " numProcess: " + str(numProcess) + " epsilon: " + str(eps) +
                              " formulaNum: " + str(fileNum) + " numMultiProcess: " + str(numMultiProcess) + " runtime: " + str(finalTime))

                        worksheet.write(row, 0, str(segmentLength/100.0))
                        worksheet.write(row, 1, str(numProcess))
                        worksheet.write(row, 2, str(eps/100.0))
                        worksheet.write(row, 3, str(compLength/100.0))
                        worksheet.write(row, 4, str(eventRate))
                        # mRuntime = mean(finalTime)
                        # stdErrRuntime = sem(runtime)
                        # errRuntime = stdErrRuntime * t.ppf((1 + 0.95) / 2, numIter - 1)
                        # print("Final Results")
                        # print("Mean: " + str(finalTime))
                        # print("Std Dev: " + str(stdErrRuntime))
                        # print("95% CI: " + str(errRuntime))
                        worksheet.write(row, 5, str(round(float(finalTime), 5)))
                        # worksheet.write(row, 6, str(round(errRuntime, 3)))
                        row = row + 1
    workbook.close()


def multi_process_func(segmentNum, segmentStart, compLength, segmentLength, fileNum, traceFile, eps):
    return_dict = []
    segmentEnd = segmentStart + segmentLength
    while segmentStart != compLength:
        runExp(fileNum, traceFile, eps, segmentStart, segmentEnd, segmentNum)

        segmentStart = segmentEnd
        segmentEnd = min(compLength, segmentEnd + segmentLength)


def runExp(fileNum, traceFile, eps, segmentStart, segmentEnd, segmentNum):
    fileName = directory + str(fileNum) + ".txt"
    numIter = 1
    # print(segmentNum)
    formulaFile = open(fileName, "r")
    listStates = []
    fromState = None
    finalAccept = None
    finalReject = None
    toState = None
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
    sumTime = 0
    totTime = 0
    startTime = 0
    for tryNum in range(numIter):
        for fromState in listStates:
            for toState in listStates:
                if fromState == toState or fromState == finalAccept or fromState == finalReject:
                    continue
                # if flag == 0:
                output1 = subprocess.getstatusoutput("python driverNew.py " + str(fileName))
                # print(output1[1])
                x = output1[1].find("OR")
                y = output1[1].find("Terminated", x)
                smtFormula = output1[1][x:y - 1]
                # print(smtFormula)
                # print("Driver: Done!")
                createTraceFile(traceFile, "traceSlice" + str(segmentNum) + ".txt", segmentStart, segmentEnd, eps)
                startTime = time.time()
                # output2 = subprocess.getstatusoutput("python checkerNew.py traceSlice.txt my_uninterpretedFunction.py " + str(eps) +
                #                                      " \"" + smtFormula + "\" \"" + AP + "\" " + str())
                output2 = subprocess.getstatusoutput("python checker.py traceSlice" + str(segmentNum) + ".txt my_uninterpretedFunction" + str(segmentNum) + ".py " + str(eps) +
                                                     " \"" + smtFormula + "\" \"" + AP + "\" " + str(fileNum))
                # print(output2[1])
                # print("Checker: Done!")
                output3 = subprocess.getstatusoutput("python my_uninterpretedFunction" + str(segmentNum) + ".py")
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
    print(str(segmentStart) + " : " + str(segmentEnd))
    print("Total time: " + str(time.time() - startTime))
    print(totTime)
    # return_dict[segmentNum] = sumTime


if __name__ == "__main__":
    directory = "formulaFiles/f"
    main(15)
    # main(40)
    # main(20)
    # main(10)
    # main(5)
    # main(2)
    # main(1)
