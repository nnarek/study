namespace Kata {
    operation Oracle_ProductWithNegation(x : Qubit[], y : Qubit, r : Bool[]) : Unit is Adj + Ctl {
        for i in 0 .. Length(x)-1 {
            if r[i] {
                ApplyControlledOnBitString([true],X,[x[i]],y);
            } else {
                ApplyControlledOnBitString([false],X,[x[i]],y);
            }
        }

    }
}