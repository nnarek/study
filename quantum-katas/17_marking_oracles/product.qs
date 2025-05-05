namespace Kata {
    operation Oracle_Product(x : Qubit[], y : Qubit, r : Bool[]) : Unit is Adj + Ctl {
        //+ sign inside circle of formula is same as XOR operation
        for i in 0 .. Length(x)-1 {
            if r[i] {
                CNOT(x[i],y);
            }
        }
    }
}
