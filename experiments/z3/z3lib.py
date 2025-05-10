from z3 import *

def Abs(x):
    return If(x >= 0,x,-x)

def Array2D(Type):
    return ArraySort(IntSort(),IntSort(), Type)

#inside RecFunction we can only call function which is declared by RecFunction, blank Function will not work