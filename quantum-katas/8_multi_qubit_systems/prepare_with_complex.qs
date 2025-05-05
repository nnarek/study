namespace Kata {
    operation PrepareWithComplex(qs : Qubit[]) : Unit is Adj + Ctl {
        //can be separated into 1/sqrt(2)(|0>+C^2|1>) TB 1/sqrt(2)(|0>+C|1>)  where C is e^(i*pi/4)
        H(qs[0]);
        H(qs[1]);

        T(qs[0]);
        T(qs[0]);
        T(qs[1]);

    }
}