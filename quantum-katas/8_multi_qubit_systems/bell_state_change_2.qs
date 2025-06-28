namespace Kata {
    operation BellStateChange2 (qs : Qubit[]) : Unit is Adj + Ctl {
        //found by exprerimentation
        //first I have applied CNOT(qs[0],qs[1]);
        //then I saw that we have 00 10 equal states and need to get 01 10
        //if we will apply X(qs[1]); then we will get 01 11 and only thing I need to do, is conditionally flip second qubit if first one is 1
        //CNOT(qs[0],qs[1]);
        //X(qs[1]);
        //CNOT(qs[0],qs[1]);

        //then I notice that all of this, is equivalent to X(qs[1]); or X(qs[0]);
        X(qs[1]);
        //this works because other qubit remain same and we flip only one of them and finally they become diferent
        //they are entangled, but it get observed only during measurement
        //during operator applications they are still independent 
    }
}