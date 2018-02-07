#!/usr/bin/python

import os
import sys
import threading
import time
import re
from subprocess import Popen, PIPE

pids = {}
p = [None, None, None]
found = False

def run_process(cmd, i):
    if (p[0] is None or p[0].poll() is None and not found):
        p[i] = Popen(cmd + sys.argv[2:], bufsize=4096, stdout=PIPE,stderr=PIPE)
        pids[p[i].pid] = i
        print("Starting child process %d (%d)" % (i,p[i].pid))

        return p[i]

def approximations():
    time.sleep(0.1)
    if p[0].poll() is None and not found:
        print("Starting approximations")
        run_process(['./q3b', sys.argv[1], '--try-underapproximations'], 1)
        run_process(['./q3b', sys.argv[1], '--try-overapproximations'], 2)

if __name__ == '__main__':
    if len(sys.argv) < 2 :
        print('Expected file name')
    else:
        run_process(['./q3b', sys.argv[1]], 0)

        t = threading.Thread(target = approximations)
        t.daemon = True
        t.start()

        i = 0;
        while (i < 4):
            (pid,exitstat) = os.wait()
            i = pids[pid]
            del pids[pid]

            print("Child Process %d (%d) terminated" % (i, pid))
            (stdout, stderr) = p[i].communicate();

            splittedOutput = stdout.strip().split()
            print("Stdout: %s" % stdout)

            if (stderr):
                print("Stderr: %s" % stderr)

            if len(splittedOutput) > 0:
                result = splittedOutput[-1]
                print("Result: %s" % result)

                if (result.startswith('sat') or result.startswith('unsat')):
                    found = True
                    for proc in p:
                        if proc is not None and proc.poll() is None:
                            proc.kill()
                    print("---------------------------")

                    m = re.search(r"Bound vars: (.*)", stdout)
                    if (m is not None):
                        print("Bound vars: %s" % m.group(1))

                    m = re.search(r"Reason: (.*)", stdout)
                    if (m is not None):
                        print("Reason: %s" % m.group(1))

                    print(result)

                    exit()
            i += 1
