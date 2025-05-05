namespace Kata {
    operation DistinguishCNOTfromSWAP (unitary : (Qubit[] => Unit is Adj + Ctl)) : Int {
        use qs = Qubit[2];
        X(qs[0]);
        X(qs[1]);
        unitary(qs);
        Reset(qs[0]);
        return if MResetZ(qs[1])==Zero {0} else {1}
        
    }
}
