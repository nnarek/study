namespace Kata {
    operation AmplitudeChange (alpha : Double, q : Qubit) : Unit is Adj + Ctl {
        // so final qubit should be (b*cosa-y*sina)|0> + (b*sina+y*cosa)|1>
        Ry(2.*alpha,q);
    }
}