namespace Kata {
    operation AllBellStates (qs : Qubit[], index : Int) : Unit is Adj + Ctl {
        H(qs[0]);
        CNOT(qs[0],qs[1]);
        if(2 <= index ){
            X(qs[0]);
        }
        if(index%2 == 1){
            Z(qs[0]);
        }
    }
}

