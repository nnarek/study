namespace Kata {
    operation AllZerosOrWState(qs : Qubit[]) : Int {
        use qt = Qubit();
        ApplyControlledOnInt(0,X,qs,qt);
        if MResetZ(qt)==One {
            return 0;
        } else {
            return 1;
        }
    }
}
