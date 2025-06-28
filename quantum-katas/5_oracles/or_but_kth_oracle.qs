namespace Kata {

    operation OrOfBitsExceptKth_Oracle(x : Qubit[], k : Int)
    : Unit is Adj + Ctl {
        use q = Qubit();
        X(q);
        H(q);
        Or_Oracle(x[0 .. k-1]+x[k+1 ...],q);//phase kickback
        H(q);
        X(q);
    }

    operation OrOfBitsExceptKth_Oracle_without_kickback(x : Qubit[], k : Int)
    : Unit is Adj + Ctl {
        use q = Qubit();
        X(q);
        SWAP(q,x[k]);
        //now x[k] is always 1
        ApplyControlledOnInt(0,X,x[0 .. k-1]+x[k+1 ...],x[k]);
        //now x[k]=0 iff others also 0
        Z(x[k]);
        ApplyControlledOnInt(0,X,x[0 .. k-1]+x[k+1 ...],x[k]);
        SWAP(q,x[k]);
        X(q);
    }

    operation Or_Oracle(x : Qubit[], y : Qubit) : Unit is Adj + Ctl {
        ApplyControlledOnInt(0,X,x,y);
        X(y);
    }
    operation KthBit_Oracle(x : Qubit[], k : Int) : Unit is Adj + Ctl {
        Z(x[k]);
    }
}
