from z3 import Solver, Int, Or, Distinct, sat, And, If
from random import randint

#seems like this code have non polynomial complexity

#input array
ai = [randint(2**16,2**20) for x in range(200)]
ai=(list)(set(ai))

#output array
ao = [ Int("x_%s" % (i+1)) for i in range(len(ai)) ]

sorted_c  = [ ao[i-1] <= ao[i] for i in range(1,len(ai)) ]

#distinct_c = [Distinct(ao)]


equal_c   = [ Or([ ao[i]==ai[j] for i in range(len(ai)) ]) 
             for j in range(len(ai)) ]

sort_c = sorted_c + equal_c#+ distinct_c 

s = Solver()
s.add( sort_c)
if s.check() == sat:
    m = s.model()
    r = [ m.evaluate(ao[i]) for i in range(len(ai))  ]
    print(r)
else:
    print("failed to solve")



