#!/usr/bin/python

import os
import sys
from subprocess import Popen, PIPE

pids = {}
p = [None, None, None]

def run_process(cmd, i):
    p[i] = Popen(cmd, stdin=PIPE, stderr=PIPE, stdout=PIPE)
    pids[p[i].pid] = i
    print "Starting child process %d (%d)" % (i,p[i].pid)

if __name__ == '__main__':
    if len(sys.argv) < 2 :
        print 'Expected file name'
    else:
        run_process(['./QuantifiedBvecToBdd', sys.argv[1]], 0)
        run_process(['./QuantifiedBvecToBdd', sys.argv[1], '--try-underapproximations'], 1)
        run_process(['./QuantifiedBvecToBdd', sys.argv[1], '--try-overapproximations'], 2)

        i = 0;
        while (i < 3):                        
            (pid,exitstat) = os.wait()
            i = pids[pid]
            del pids[pid]

            print "Child Process %d (%d) terminated" % (i, pid)
            (stdout, stderr) = p[i].communicate();

            splittedOutput = stdout.strip().split()
            
            if len(splittedOutput) > 0:
                result = splittedOutput[-1]
                print "Result: %s" % result

                if (result.startswith('sat') or result.startswith('unsat')):
                    for proc in p:
                        if proc.poll():
                            proc.terminate()                        
                    print "---------------------------"
                    print result
                        
                    break                
                
            i += 1
        
