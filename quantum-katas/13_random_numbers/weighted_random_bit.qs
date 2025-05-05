namespace Kata {
    import Std.Math.Sqrt;
    import Std.Math.ArcCos;
    operation WeightedRandomBit(x : Double) : Int {
        use q = Qubit();
        Ry(2.0*ArcCos(Sqrt(x)),q);
        let res = MResetZ(q);
        if res == One {
            return 1;
        } else {
            return 0;
        }
    }
}
