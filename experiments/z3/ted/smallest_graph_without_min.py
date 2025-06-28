from z3 import *

n = Int("n")#number of nodes

is_edge=Function("e",IntSort(),IntSort(),IntSort(),BoolSort())

x,y,N = Ints("x y N")

c1=[  ForAll([x,y,N],is_edge(x,y,N)==is_edge(y,x,N))  ]#undirected graph
c5=[  ForAll([x,N],Not(is_edge(x,x,N)))  ]#no self cycles

numberOfNodes = Function('numberOfNodes',IntSort(),IntSort(),IntSort(),IntSort())#number of neighbours of z node,i always should be equal to n-1
i,z,k = Ints('i z k')
c6=[  ForAll([z,k],numberOfNodes(z,-1,k)==0)  ]
c7=[  ForAll([i,z,k],Implies(And(i>=0,i<k),numberOfNodes(z,i,k)==numberOfNodes(z,i-1,k)+is_edge(z,i,k)))  ]

def get_cond(n):

    c2=[  n>=0  ]

    c3=[  numberOfNodes(0,n-1,n)==1  ]
    c4=[  ForAll([z],Implies(z>0,numberOfNodes(z,n-1,n)==3))  ]
    return  And(c2+c3+c4)

#s = Optimize()
#s.add(get_cond(n))
#s.minimize(n)

s = Solver()
s.add(c1+c5+c6+c7)
m = Int("m")
#s.add(And(get_cond(n),ForAll(m,Implies(And(0<=m,m<n),Not(get_cond(m)))) ))
s.add(ForAll(m,Implies(And(0<=m,m<6),Exists(is_edge,Not(get_cond(m))))))
#TODO write minimizer
#solver is able to find solution when I give hint that n==6
#but solver can not find solution when I say that n<7,n>=0,
#then I notice that is_edge  function should be different for each m,but adding new param does not help
#maybe it does not help because for one of its values N function does not exist 
print(s)
if s.check() == sat:
    m = s.model()
    print(m)
    n=m[n].as_long()
    for x in range(n):
        print(str(x)+" -> ",[y for y in range(n) if m.evaluate(is_edge(x,y)) ])
else:
    print("failed to solve")
