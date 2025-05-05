namespace Kata {
    operation ThreeQuartersPiPhase (q : Qubit) : Unit is Adj + Ctl {
        T(q);
        T(q);
        T(q);
    }
}