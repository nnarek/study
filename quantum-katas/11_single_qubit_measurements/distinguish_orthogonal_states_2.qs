namespace Kata {
    import Std.Math.ArcTan2;
    operation IsQubitA(alpha : Double, q : Qubit) : Bool {
        Rx(-2.0*alpha,q);
        let res = M(q);
        if res == Zero {
            return true;
        } else {
            return false;
        }
    }
}
