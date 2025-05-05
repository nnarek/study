namespace Kata {
    operation Oracle_Parity(x : Qubit[], y : Qubit) : Unit is Adj + Ctl {
        for i in 0 .. Length(x)-1 {
            CNOT(x[i],y);
        }
    }
}
