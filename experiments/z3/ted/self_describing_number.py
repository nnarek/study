from z3 import *

N=9

X = [ Int("x_%s" % (j+1)) for j in range(N)  ]

cells_c  = [ Sum([X[i]==j for i in range(N)])==X[j] for j in range(N) ]


sudoku_c = cells_c


s = Solver()
r=[]
s.add(sudoku_c )
if s.check() == sat:
    m = s.model()
    r = [ m.evaluate(X[j]) for j in range(N) ]
    print(r)
else:
    print("failed to solve")

s.add([r[i]!=X[i] for i in range(N)] )

if s.check() == sat:
    m = s.model()
    r = [ m.evaluate(X[j]) for j in range(N) ]
    print(r)
else:
    print("there are no other solutions ")
