import re
import fileinput
import sys

p = re.compile('\d+\.\d+\.\d+')

# workaround for broken -i flag
opts = {'2.9.1':'-Yrepl-sync', '2.9.2':'-Yrepl-sync'}

for line in fileinput.input():
    m = p.search(line)
    if m:
        res = m.group()
        if res in opts :
            print opts[res]
        exit(0)
    else:
        sys.stderr.write("asked for scala version; got this:\n" + line)
        exit(1)
        
