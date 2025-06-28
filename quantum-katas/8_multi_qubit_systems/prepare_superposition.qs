namespace Kata {
    operation PrepareSuperposition(qs : Qubit[]) : Unit is Adj + Ctl {
        //first qubit is unchanged
        //second qubit have state |+>
        X(qs[1]);
        H(qs[1]);
    }
}