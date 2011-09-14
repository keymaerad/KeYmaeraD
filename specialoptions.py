import re
import fileinput
p = re.compile('\d+\.\d+\.\d+')

# workaround for broken -i flag
opts = {'2.9.1':'-Yrepl-sync'}

for line in fileinput.input():
    m = p.search(line)
    if m:
        res = m.group()
        if res in opts :
            print opts[res]
        exit(0)
    else:
        print "what"
        exit(0)
        
