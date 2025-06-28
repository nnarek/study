namespace Kata {
    operation TwoBitstringsMeasurement(qs : Qubit[], bits1 : Bool[], bits2 : Bool[]) : Int {
        for i in 0 .. Length(qs)-1 {
            if bits1[i]!=bits2[i] {
                return if (M(qs[i])==One)==bits1[i] {0} else {1};
            }
        }
        return -1;
    }
}
