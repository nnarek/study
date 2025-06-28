namespace Kata {
    operation IsSeven_PhaseOracle(x : Qubit[]) : Unit is Adj + Ctl {
        ApplyControlledOnBitString([true,true],Z,x[0 .. 1],x[2]);

    }
}