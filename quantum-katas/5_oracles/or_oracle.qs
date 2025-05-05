namespace Kata {
    operation Or_Oracle(x : Qubit[], y : Qubit) : Unit is Adj + Ctl {
        ApplyControlledOnInt(0,X,x,y);
        X(y);
    }
}
