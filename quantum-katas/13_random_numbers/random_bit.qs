namespace Kata {
    import Std.Convert.BoolArrayAsInt;
    operation RandomBit() : Int {
        use q = Qubit();
        H(q);
        return BoolArrayAsInt([MResetZ(q)==One]);
    }

}