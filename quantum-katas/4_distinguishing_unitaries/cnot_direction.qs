namespace Kata {
    operation CNOTDirection (unitary : (Qubit[] => Unit is Adj + Ctl)) : Int {
        use qs = Qubit[2];
        X(qs[0]);
        X(qs[1]);
        unitary(qs);
        Reset(qs[1]);
        return if MResetZ(qs[0])==Zero {1} else {0}
        
    }
}
