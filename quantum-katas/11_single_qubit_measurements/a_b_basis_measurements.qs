namespace Kata {
    operation MeasureInABBasis(alpha : Double, q : Qubit) : Result {
        Rx(-2.0*alpha,q);//replace from A B basis vectors by pauliZ basis vectors,leaving amplitudes same
        let res = M(q);
        Rx(2.0*alpha,q);//replacing basis vectors back
        return res;
    }
}