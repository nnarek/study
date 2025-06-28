namespace Kata {
    import Std.Math.BitSizeI;
    operation RandomNumberInRange(min : Int, max : Int) : Int {
        //used rejection sampling
        let range = max - min;
        let range_log2 = BitSizeI(range);
        let rand = RandomNBits(range_log2);
        if rand <= range {
            return min + rand;
        } else {
            return RandomNumberInRange(min,max);
        }
    }

    // You can use the operations defined in the earlier exercises to implement your solution.
    operation RandomBit() : Int {
        use q = Qubit();
        H(q);
        return MResetZ(q) == Zero ? 0 | 1;
    }

    operation RandomNBits(N : Int) : Int {
        mutable result = 0;
        for i in 0 .. N - 1 {
            set result = result * 2 + RandomBit();
        }
        return result;
    }
}