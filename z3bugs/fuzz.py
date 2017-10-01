import re
import random
import os

has_rlimit = re.compile("rlimit (\d+)")

def fuzz(f):
    rand = random.Random()
    ins = open(f)
    f1 = "%s.tmp.smt2" % f
    ous = open(f1, 'w')
    line = ins.readline()
    while line:
       m = has_rlimit.search(line)
       if m:
          num = int(m.group(1))
          num1 = num/2 + rand.randint(0, num)
          line = line.replace(m.group(1), "%d" % num1)
       ous.write(line)           
       line = ins.readline()
    ins.close()
    ous.close()
    os.system("move %s %s" % (f1, f))
    os.system("z3.exe %s" % f)

while True:
   fuzz("logfile-01.smt2") 