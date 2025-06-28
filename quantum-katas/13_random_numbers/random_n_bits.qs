namespace Kata {
    operation RandomNBits(N : Int) : Int {
        mutable pow = 1;
        mutable res = 0;
        for i in 1 .. N {
            res += pow*RandomBit();
            pow *= 2;
        }
        return res;
    }

    // You can use the operation defined in the first exercise to implement your solution.
    operation RandomBit() : Int {
        use q = Qubit();
        H(q);
        return MResetZ(q) == Zero ? 0 | 1;
    }
}
