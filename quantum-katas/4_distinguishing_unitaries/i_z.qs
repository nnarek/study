namespace Kata {
    operation DistinguishIfromZ(unitary : (Qubit => Unit is Adj + Ctl)) : Int {
        use qt = Qubit();
        H(qt);//we have |+> state
        unitary(qt);
        if Measure([PauliX],[qt])==One {//state was changed to |->
            H(qt);
            X(qt);
            return 1;
        } else {
            H(qt);
            return 0;
        }
    }
}
