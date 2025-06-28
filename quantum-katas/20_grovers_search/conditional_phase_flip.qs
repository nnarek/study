namespace Kata {
    operation ConditionalPhaseFlip(qs : Qubit[]) : Unit is Adj + Ctl {
        within{
            ApplyToEachA(X,qs);
        } apply {
            Z(qs[0]);
            X(qs[0]);
            Z(qs[0]);
            X(qs[0]);
            Controlled Z(qs[1 ...],qs[0]);
        }

    }
}
