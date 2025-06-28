from z3 import *

N=5

f=[Function("f_%s" % (i+1), *[BoolSort() for x in range(N)]) for i in range(N)]

r = [ Bool("r_%s" % (j+1)) for j in range(N)  ]#their answers

a = [ Bool("a_%s" % (j+1)) for j in range(N)  ]#actual hat color


cond1 = [ f[j](*r[j+1:N],*a[:j])==r[j] for j in range(N) ]

cond2 = ForAll(a,Exists(r,And(cond1 + [ a[j]==r[j] for j in range(N-1) ])))#if we will not write "Exist r" then z3 will assume that r is global constant for all possible values of a 

print(cond2) 
s = Solver()
s.add(cond2)
if s.check() == sat:
    m = s.model()
    print(m)
    #n=2
    #print(m.evaluate(f[n](False,False)))
    #print(m.evaluate(f[n](False,True)))
    #print(m.evaluate(f[n](True,False)))
    #print(m.evaluate(f[n](True,True)))#he found nxor in this version of z3
else:
    print("failed to solve")
