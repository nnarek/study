namespace Kata {
    operation DistinguishHfromX(unitary : (Qubit => Unit is Adj + Ctl)) : Int {
        // definition hinted me that I need to use gate twice
        // looking at my internal table of properties of various gates I notice that HXH=Z and XXX=X
        // V^+ ZX V = [a b][b -a]^T = ab - ab = 0 for all a and b, which means that any state produce orthogonal state after application of X and Z gates
        // so for simplicity let choose |0> as initial state

        use qt = Qubit();
        unitary(qt);
        X(qt);
        unitary(qt);
        if M(qt)==Zero {//we applied Z
            return 0;
        } else { //we aplied X
            X(qt);
            return 1;
        }
    }
}
