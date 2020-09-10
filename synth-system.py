import sys
import threading
from queue import Queue
import numpy as np
import time


def compute(stuffs):
    trace = ""
    for i in range(0, len(stuffs)):
        r = int(np.random.uniform(0, 2))
        if r == 0:
            trace = trace + stuffs[i]
    return trace


def timeSendOrLocal(pTime, lTime, cTime):
    lpTime = lTime
    lTime = max(lpTime, pTime)
    if lTime == lpTime:
        cTime = cTime + 1
    else:
        cTime = 0
    return lTime, cTime


def timeReceive(pTime, lTime, cTime, lmTime, cmTime):
    lpTime = lTime
    lTime = max(lpTime, lmTime, pTime)
    if lTime == lpTime and lpTime == lmTime:
        cTime = max(cTime, cmTime) + 1
    elif lTime == lpTime:
        cTime = cTime + 1
    elif lTime == lmTime:
        cTime = cmTime + 1
    else:
        cTime = 0
    return lTime, cTime


def SendMessage(fromProcess, toProcess, fromTime):
    print("hi")


def process(num, msg, EType, EValue, ETime, PTime):
    phTime = time.time()
    loTime = 0
    caTime = 0
    # global threadLock
    # while True:
    # _threadLock.acquire()
    Time = [0, 0, 0]
    # Physical time is in microsecond!
    Time[0] = PTime
    # if Time[0] >= 100:
    #     break
    # logicalClock[num] = Time[0]
    # while True:
    #     mini = logicalClock[num]
    #     maxi = logicalClock[num]
    #     for j in logicalClock:
    #         if mini > j:
    #             mini = j
    #         if maxi < j:
    #             maxi = j
    #     if abs(logicalClock[num] - mini) <= epsilon and abs(logicalClock[num] - maxi) <= epsilon:
    #         break

    # compute('SELECT * FROM students')
    if msg[num].empty():
        work = int(np.random.uniform(1, 10))
    else:
        work = 0
    if numProcess == 1:
        work = 2
    if work == 1 and not (msg[1 - num].full()):
        # sending a msg
        EType.put("S")
        time.sleep(0.49)
        EValue.put("ALL")
        loTime, caTime = timeSendOrLocal(Time[0], loTime, caTime)
        for j in range(0, numProcess):
            if j == num:
                continue
            msg[j].put("Sender " + str(num) + " ::Time:: " + "" + str(Time[0]) + "," + str(loTime) + "," + str(caTime))

    elif work == 0 and not (msg[num].empty()):
        # receiving a msg
        s = msg[num].get().split()
        s1 = s[3].split(',')
        loTime, caTime = timeReceive(Time[0], loTime, caTime, int(s1[1]), int(s1[2]))
        EType.put("R")
        EValue.put(s[3])
        time.sleep(0.49)
    else:
        EType.put("C")
        loTime, caTime = timeSendOrLocal(Time[0], loTime, caTime)
        trace = compute("pqrszt")
        trace = compute("ab")
        EValue.put(trace)
        time.sleep(0.49)
    Time[1] = loTime
    Time[2] = caTime
    ETime.put(Time)
    print("Thread " + str(num) + " : " + str(Time))
    # time.sleep(sleepTime)
    # _threadLock.release()


def writeFile(EType, EValue, ETime):
    file = open(fileName, "w")
    file.write("<System>\n")
    for num1 in range(0, numProcess):
        file.write("\t<Process>\n")
        num2 = 0
        while not EType[num1].empty():
            num2 = num2 + 1
            file.write("\t\t<Event name = \"" + str(num1 + 1) + "_" + str(num2) + "\", ")
            file.write("type = \"{0}\", ".format(EType[num1].get()))
            file.write("value = \"{0}\", ".format(EValue[num1].get()))
            file.write("time = \"{0}\"".format(str(ETime[num1].get())))
            file.write(">\n")
        file.write("\t<\\Process>\n")
    file.write("<\\System>")
    file.close()


def main():
    processList = [None] * numProcess
    msg = []
    EType = []
    EValue = []
    ETime = []
    PTime = []

    for i in range(0, numProcess):
        msg.append(Queue(2000))
        EType.append(Queue(2000))
        EValue.append(Queue(2000))
        ETime.append(Queue(2000))
        PTime.append(0)

    # maxTime is denoted in 10^(-2) seconds
    # maxTime = 300
    while True:
        i = int(np.random.choice(list(range(0, numProcess))))
        # if PTime[i] != 0:
        #     PTime[i] = int((time.time() - timeStart) * 100000)
        if PTime[i] <= maxTime:
            timeStart = time.time()
            process(i, msg, EType[i], EValue[i], ETime[i], PTime[i])
            PTime[i] = PTime[i] + int(abs(time.time() - timeStart) * 100)
        flag = 0
        for j in range(numProcess):
            if PTime[j] > maxTime:
                flag = flag + 1
        if flag == numProcess:
            break

    # for i in range(0, numProcess):
    #     processList[i].start()
    #
    # for i in range(0, numProcess):
    #     processList[i].join()
    # print("joined")

    writeFile(EType, EValue, ETime)


if __name__ == "__main__":
    if len(sys.argv) == 4:
        numProcess = int(sys.argv[1])
        maxTime = int(sys.argv[2])
        # numProcess = 10
        # sleepTime = 1
        fileName = sys.argv[3]
        # _threadLock = threading.Lock()
        # logicalClock = [0] * numProcess
        main()
    else:
        print("<int1> <int2> <fileName> \t numProcess = <int1>, Time Sync Epsilon = <int2>")
