namespace Kata {
    operation Oracle_BitSumDivisibleBy3 (x : Qubit[], y : Qubit) : Unit is Adj + Ctl {
        use qstate3 = Qubit[2];
        within {
            for i in 0 .. Length(x)-1 {
                Controlled increament_mod3([x[i]],qstate3);
            }
        } apply {
            ApplyControlledOnInt(0,X,qstate3,y);
        }
    }

    operation increament_mod3 (c : Qubit[]) : Unit is Adj + Ctl {
        // we want to do following inplace transitions without aux qubits
        //01            00          10
        //10            01          00
        //there is few available operations, lets try to brute force them

        //if we will apply CNOT(c[0],c[1]); then we will get 
        //01            00          11
        //if instead we will apply CNOT0(c[0],c[1]) then we will get, note this one is near desired state
        //00            01          10

        //if we will apply CNOT0(c[1],c[0]) to above state then we will get disired state
        //10            01          00

        ApplyControlledOnBitString([false],X,[c[0]],c[1]);
        ApplyControlledOnBitString([false],X,[c[1]],c[0]);
    }

    operation increament_mod3_auxQubit (c : Qubit[]) : Unit is Adj + Ctl {
        use temp_state = Qubit[2];

        //try to use ApplyPauliFromInt
        ApplyControlledOnInt(1,X,c,temp_state[0]);//01->10
        ApplyControlledOnInt(0,X,c,temp_state[1]);//00->01
        //10->00

        SWAP(temp_state[0],c[0]);
        SWAP(temp_state[1],c[1]);
        //now temp_state is previous state and we need to uncompute it
        ApplyControlledOnInt(0,X,c,temp_state[0]);
        ApplyControlledOnInt(2,X,c,temp_state[1]);
    }
}