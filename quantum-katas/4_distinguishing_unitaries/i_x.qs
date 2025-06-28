namespace Kata {
    operation DistinguishIfromX(unitary : (Qubit => Unit is Adj + Ctl)) : Int {
        use qt = Qubit();
        unitary(qt);
        if M(qt)==One {
            Adjoint unitary(qt);
            return 1;
        } else {
            return 0;
        }
    }
}
