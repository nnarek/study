namespace Kata {
    operation RandomTwoBits() : Int {
        return 2*RandomBit()+RandomBit();
    }

    // You can use the operation defined in the previous exercise to implement your solution.
    operation RandomBit() : Int {
        use q = Qubit();
        H(q);
        return MResetZ(q) == Zero ? 0 | 1;
    }
}
