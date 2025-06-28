namespace Kata {
    operation PrepareWithReal(qs : Qubit[]) : Unit is Adj + Ctl {
        //qubits are separable and first one have |-> state and second one |+> state
        // 1/sqrt(2)(|0>+|1>) TB 1/sqrt(2)(|0>-|1>)  where TB is tensor product
        X(qs[1]);
        H(qs[0]);
        H(qs[1]);
    }
}