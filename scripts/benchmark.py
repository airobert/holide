#!/usr/bin/env python

import os
import subprocess
import time
import sys

def basename(filename):
  return os.path.splitext(os.path.basename(filename))[0]

command = sys.argv[1]
files = sys.argv[2:]

# Maximum width of the names to display
ptime = 0
fsize = 0
ct = 0
width = max(map(len, map(basename, files))) 
files.sort(key=basename)
for filename in files:
  ct = ct + 1
  name = basename(filename)
  size = os.path.getsize(filename)
  fsize = fsize + size
  start = time.time()
  code = subprocess.call(["bash", "-c", "%s %s > /dev/null 2>&1" % (command, filename)])
  end = time.time()
  ptime = ptime + (end - start) 
  if code == 0:
    print("%-*s  %10d  %04.2f" % (width, name, size, end - start))
  else:
    print("%-*s  %10d  FAIL" % (width, name, size))
  
print("total proof checking time = %04.2f" % (ptime))
print("total dk file size = %10d" % (fsize))
print("in total %10d files" % ct)