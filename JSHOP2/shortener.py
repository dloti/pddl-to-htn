import math
import argparse

parser = argparse.ArgumentParser()
parser.add_argument('-p', '--path', help='path to the domain')
args = parser.parse_args()

f = open(args.path+'problem.java','r')
lines = f.readlines()
f.close()

methodcnt = 0
helperlines = []
insidemethod = False
with open(args.path+'problem.java','w') as f:
    for line in lines:
        if insidemethod:
            helperlines.append(line)
        else:
            f.write(line)

        if insidemethod and line == '\t}\n' and not line.__contains__('s.add('):
            insidemethod = False
            cnt = len(helperlines)
            if cnt == 0:
                break
            methodcnt = int(math.ceil(cnt/200.))
            for i in range(0,methodcnt):
                f.write('\t\tstateHelper'+str(i)+'(s);\n')
            f.write(line)
            cnt = 0
            for i in range(0,len(helperlines)):
                if i%200 == 0:
                    if i != 0:
                        f.write('\t}\n\n')
                    f.write('\tprivate static void stateHelper'+str(cnt)+'(State s)	{\n')
                    cnt+=1
                f.write(helperlines[i])

        if not insidemethod and line.__contains__('private static void createState0(State s)	{'):
            insidemethod = True

#print(len(helperlines))
#print(methodcnt)
