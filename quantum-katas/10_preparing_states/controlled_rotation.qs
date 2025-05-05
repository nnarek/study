namespace Kata {
    operation ControlledRotation (qs : Qubit[]) : Unit is Adj + Ctl {
        H(qs[0]);
        ApplyControlledOnBitString([true],H,[qs[0]],qs[1]);
    }  
}

