namespace Kata {
    operation ZeroZeroOrOneOne(qs : Qubit[]) : Int {
        if M(qs[0]) == Zero {
            return 0;
        } else {
            return 1;
        }
    }
}
