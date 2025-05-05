namespace Kata {
    operation IsPlusPlusMinus(qs : Qubit[]) : Int {
        let res0 = Measure([PauliX],[qs[0]]);
        if res0 == Zero {
            // this mean that first qubit have + state and initially it is also have + state
            return 0;
        } else {
            return 1;
        }
    }
}