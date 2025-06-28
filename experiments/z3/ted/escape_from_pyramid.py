from z3 import *


N=9 #number of persons
L=2 #number of liers
D=4 #number of doors

t = [ Bool("t_%s" % (j+1)) for j in range(N)  ]

c1=[ t[0]==True ]
c2=[ Sum(t)>=(N-L) ]

x = Int("x")

c4=[  And(0<=x,x<D) ]

doors = [ Int("doors_%s" % (j+1)) for j in range(N)  ]

c3=[ And(0<=d,d<D) for d in doors ]

#c5=[ And(doors[0]==0,doors[1]==1,doors[2]==1,doors[3]==2,doors[4]==2,doors[5]==2) ] #TODO returns sat,but without providing hint z3 are not able to find solution and return unknown after 90 min
c5=[]

f = Function("f", *([BoolSort() for x in range(N)]+[IntSort()]))

cond=[  ForAll(t+[x],Implies(And(c1+c2+c4),And(f([ (doors[n]==x)==t[n] for n in range(N) ])==x,And(c3+c5))))  ]


s = Solver()
s.add(cond)
if s.check() == sat:
    m = s.model()
    print(s)

print(s.check())
