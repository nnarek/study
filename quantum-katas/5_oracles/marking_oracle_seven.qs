namespace Kata {
    operation IsSeven_MarkingOracle(x : Qubit[], y : Qubit) : Unit is Adj + Ctl {
        ApplyControlledOnBitString([true,true,true],X,x,y);

    }
}
