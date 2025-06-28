namespace Kata {
    operation MinusState(q : Qubit) : Unit is Adj + Ctl {
        H(q);
        Z(q);
    }
}
