namespace Kata {
    import Std.Math.*;

    operation PrepareRotatedState(alpha : Double, beta : Double, q : Qubit) : Unit is Adj + Ctl {
        Rx(2.*ArcTan2(beta,alpha),q);
    }
}