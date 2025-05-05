namespace Kata {
    operation PhaseOracle_OneMinusX (x : Qubit) : Unit is Adj + Ctl {
        X(x);
        Z(x);
        X(x);
    }
}
