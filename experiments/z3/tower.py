from z3 import Solver, Int, Or, Distinct, sat, And, If, Exists


left=[0,1,3,0,0,0]
right=[3,0,3,0,0,0]
top=[0,0,0,0,6,4]
butt=[3,0,3,3,0,0]

N=len(left)

X = [ [ Int("x_%s_%s" % (i+1, j+1)) for j in range(N) ] 
      for i in range(N) ]

known = [
    #X[4][2]==2
]


cells_c  = [ And(1 <= X[i][j], X[i][j] <= N) 
             for i in range(N) for j in range(N) ]

rows_c   = [ Distinct(X[i]) for i in range(N) ]


cols_c   = [ Distinct([ X[i][j] for i in range(N) ]) 
             for j in range(N) ]




def is_visible(a,n):
    if len(a)<=1:
        if n==len(a):
            return True
        else:
            return False
    return If(a[0]<a[1], is_visible(a[1:],n-1), is_visible([a[0]]+a[2:],n) )

left_c=[ is_visible(X[i],left[i]) for i in range(N) if left[i]!=0 ]
right_c=[ is_visible(X[i][::-1],right[i]) for i in range(N) if right[i]!=0 ]

top_c   = [ is_visible([X[i][j] for i in range(N)],top[j]) for j in range(N) if top[j]!=0]
butt_c=[ is_visible([X[i][j] for i in range(N)][::-1],butt[j]) for j in range(N) if butt[j]!=0]

c = cells_c + rows_c + cols_c + left_c + right_c + top_c + butt_c + known

s = Solver()
s.add(c)
if s.check() == sat:
    m = s.model()
    r = [ [ m.evaluate(X[i][j]) for j in range(N) ] for i in range(N) ]
    for x in r:
        print(x)
else:
    print("failed to solve")



