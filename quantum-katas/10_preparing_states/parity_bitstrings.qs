namespace Kata {
    operation AllStatesWithParitySuperposition (qs : Qubit[], parity : Int) : Unit is Adj + Ctl {
        // we can think about this problem by using dynamic programming
        // if we know solution for N qubits and want to add new qubit, 
        // then we need to add |0> state to AllStatesWithParitySuperposition(N,parity) in 1/2 cases 
        // and |1> state to AllStatesWithParitySuperposition(N,1-parity) in 1/2 cases
        if(Length(qs) == 1){
            if(parity==1) {
                X(qs[0]);
            } 
        } else {
            H(qs[0]);
            ApplyControlledOnInt(0,AllStatesWithParitySuperposition,[qs[0]],(Std.Arrays.Rest(qs),parity));
            ApplyControlledOnInt(1,AllStatesWithParitySuperposition,[qs[0]],(Std.Arrays.Rest(qs),1-parity));
        }
    }
}