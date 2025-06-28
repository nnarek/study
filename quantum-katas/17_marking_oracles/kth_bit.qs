namespace Kata {
    operation Oracle_Kth_Bit(x : Qubit[], y : Qubit, k : Int) : Unit is Adj + Ctl {
        ApplyControlledOnBitString([true],X,[x[k]],y)

    }
}
