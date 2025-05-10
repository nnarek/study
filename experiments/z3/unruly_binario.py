from z3 import Solver, Int, Or, Distinct, sat, And, If, Bool, Sum, Not

N=10
instance = "bbAHCDacejcdInbbhGBDAcab"

X = [ [ Int("x_%s_%s" % (i+1, j+1)) for j in range(N) ] 
      for i in range(N) ]

cells_c  = [ And(0 <= X[i][j], X[i][j] <= 1) 
             for i in range(N) for j in range(N) ]

rows_c   = [ Sum(X[i])==(N//2) for i in range(N) ]

cols_c   = [ Sum([ X[i][j] for i in range(N) ])==(N//2) 
             for j in range(N) ]

row_neightbour = [ Not(And(X[i][j] == X[i][j+1],X[i][j] == X[i][j+2]))
               for i in range(N) for j in range(N-2) ]

column_neightbour = [ Not(And(X[i][j] == X[i+1][j],X[i][j] == X[i+2][j]))
               for i in range(N-2) for j in range(N) ]

#TODO add constraint that rows and columns are distinct
#it is additional constraint  of binario

instance_c = []

r=0
c=-1
for x in instance[:-1 ]:
    c+=(ord(x.lower())-ord('a')+1)
    r+=(c//N)
    c=(c%N)
    print(r,c)
    instance_c.append( X[r][c]==(x!=x.lower()) )
        
sudoku_c = cells_c + rows_c + cols_c  + row_neightbour + column_neightbour + instance_c

s = Solver()
s.add(sudoku_c)
if s.check() == sat:
    m = s.model()
    r = [ [ m.evaluate(X[i][j]) for j in range(N) ] 
          for i in range(N) ]
    for x in r:
        print(x)
else:
    print("failed to solve")



