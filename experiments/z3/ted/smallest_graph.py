from z3 import *

n = Int("n")#number of nodes

is_edge=Function("e",IntSort(),IntSort(),BoolSort())

x,y = Ints("x y")

c1=[  ForAll([x,y],is_edge(x,y)==is_edge(y,x))  ]#undirected graph
c5=[  ForAll([x],Not(is_edge(x,x)))  ]#no self cycles
c2=[  n>=0  ]


numberOfNodes = Function('numberOfNodes',IntSort(),IntSort(),IntSort())#number of neighbours of z node,i always should be equal to n-1
i,z = Ints('i z')
c6=[  ForAll(z,numberOfNodes(z,-1)==0)  ]
c7=[  ForAll([i,z],Implies(And(i>=0,i<n),numberOfNodes(z,i)==numberOfNodes(z,i-1)+is_edge(z,i)))  ]


c3=[  numberOfNodes(0,n-1)==1  ]
c4=[  ForAll(z,Implies(z>0,numberOfNodes(z,n-1)==3))  ]


s = Optimize()
s.add(c1+c2+c3+c4+c5+c6+c7)
s.minimize(n)
if s.check() == sat:
    m = s.model()
    n=m[n].as_long()
    for x in range(n):
        print(str(x)+" -> ",[y for y in range(n) if m.evaluate(is_edge(x,y)) ])
else:
    print("failed to solve")
