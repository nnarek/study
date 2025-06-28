namespace Kata {
    import Std.Math.*;

    operation PrepareArbitraryState(
        alpha : Double,
        beta : Double,
        theta : Double,
        q : Qubit
    ) : Unit is Adj + Ctl {
        Ry(2.*ArcTan2(beta,alpha),q);
        R1(theta,q);
    }
}