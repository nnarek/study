from z3 import *

d1 = [ Int("d1_%s" % (j+1)) for j in range(6) ]
d2 = [ Int("d2_%s" % (j+1)) for j in range(6) ]

c1 = [ And(1<=d,d<=4) for d in d1 ]
c2 = [ 1<=d for d in d2 ]

cart = [ a+b for a in d1 for b in d2]
dcart= [ a+b for a in range(1,7) for b in range(1,7)]

def same(a,b):
    return [Sum([x==y for x in a ])==Sum([x==y for x in b ]) for y in b ]

c3=same(cart,dcart)

c4=[Sum(d1)+Sum(d2)==6*7]

cond=c1+c2+c3+c4

s = Solver()
s.add(cond)
if s.check() == sat:
    m = s.model()
    r1 = [ m.evaluate(j).as_long() for j in d1 ]
    r2 = [ m.evaluate(j).as_long() for j in d2 ]
    print(r1,r2)

else:
    print("failed to solve")


#TODO find are there any other solution
