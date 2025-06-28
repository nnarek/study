namespace Kata {
    operation AntiControlledGate (qs : Qubit[]) : Unit is Adj + Ctl {
        X(qs[0]);
        CNOT(qs[0],qs[1]);
        X(qs[0]);

        //or it is same as 
        //ApplyControlledOnBitString([false],X,[qs[0]],qs[1]);
    }
}