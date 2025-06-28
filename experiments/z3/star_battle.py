from z3 import Solver, Int, Or, Distinct, sat, And, If, Bool, Sum, Not

#183 extreme hard
instance = ((0,0,0,1,1,1,8,8,8),
            (0,0,2,1,1,1,1,8,8),
            (0,0,2,1,1,1,1,5,5),
            (0,2,2,5,5,5,5,5,7),
            (2,2,2,5,5,5,5,7,7),
            (3,3,5,5,5,6,5,7,7),
            (3,3,3,5,4,6,6,6,6),
            (3,3,3,4,4,6,6,6,6),
            (4,4,4,4,4,4,6,6,6))

X = [ [ Int("x_%s_%s" % (i+1, j+1)) for j in range(9) ] 
      for i in range(9) ]

cells_c  = [ And(0 <= X[i][j], X[i][j] <= 1) 
             for i in range(9) for j in range(9) ]

rows_c   = [ Sum(X[i])==2 for i in range(9) ]

cols_c   = [ Sum([ X[i][j] for i in range(9) ])==2 
             for j in range(9) ]

cells=[[] for x in range(9)]
for x in range(9):
    for y in range(9):
        cells[instance[x][y]].append(X[x][y])

sq_c     = [ Sum(cells[i])==2 for i in range(9) ]

#TODO use more simple statements 
row_neightbour = [ Not(And(X[i][j] == 1,X[i][j+1]==1))
               for i in range(9) for j in range(8) ]

column_neightbour = [ Not(And(X[i][j] == 1,X[i+1][j]==1))
               for i in range(8) for j in range(9) ]

diaganl1_neightbour = [ Not(And(X[i][j] == 1,X[i+1][j+1]==1))
               for i in range(8) for j in range(8) ]

diaganl2_neightbour = [ Not(And(X[i][j] == 1,X[i+1][j-1]==1))
               for i in range(8) for j in range(1,9) ]

sudoku_c = cells_c + rows_c + cols_c + sq_c + row_neightbour + column_neightbour+diaganl1_neightbour +diaganl2_neightbour

s = Solver()
s.add(sudoku_c)
if s.check() == sat:
    m = s.model()
    r = [ [ m.evaluate(X[i][j]) for j in range(9) ] 
          for i in range(9) ]
    for x in r:
        print(x)
else:
    print("failed to solve")



