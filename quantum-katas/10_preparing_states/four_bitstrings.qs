namespace Kata {
    operation FourBitstringSuperposition (qs : Qubit[], bits : Bool[][]) : Unit {
        use qtemp = Qubit[2];
        H(qtemp[0]);
        H(qtemp[1]);

        for biti in 0 .. 3 {
            for i in 0 .. Length(qs) - 1 {
                if(bits[biti][i]){
                    ApplyControlledOnInt(biti,X,qtemp,qs[i]);
                }
            }
        }
        //for bits[0] we already know that qtemp have |00> state
        ApplyControlledOnBitString(bits[1],X,qs,qtemp[0]);
        ApplyControlledOnBitString(bits[2],X,qs,qtemp[1]);
        ApplyControlledOnBitString(bits[3],X,qs,qtemp[0]);
        ApplyControlledOnBitString(bits[3],X,qs,qtemp[1]);
    }
}