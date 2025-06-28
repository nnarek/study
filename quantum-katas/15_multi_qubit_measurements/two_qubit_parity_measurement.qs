namespace Kata {
    operation ParityMeasurement(qs : Qubit[]) : Int {
        let res0 = Measure([PauliZ,PauliZ],qs);
        if res0 == Zero {
            return 0;
        } else {
            return 1;
        }
    }
}