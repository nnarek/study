namespace Kata {
    operation Oracle_PeriodicGivenPeriod (x : Qubit[], y : Qubit, p : Int) : Unit is Adj + Ctl {
        within {
            //switching all qubits after p-rd qubit 
            for i in p .. Length(x)-1 {
                ApplyControlledOnInt(1,X,[x[i%p]],x[i]);
            }
        } apply {
            //if string is P periodic then after p-rd qubit, all qubits should be 0
            ApplyControlledOnInt(0,X,x[p ...],y);
        }
    }    
    operation Oracle_PeriodicGivenPeriod_aux_qubit (x : Qubit[], y : Qubit, p : Int) : Unit is Adj + Ctl {
        use qt = Qubit[p];
        within {
        for pi in 0 .. p-1 {
            X(qt[pi]);
            let qp = getEachPeriodN(x[pi ...],p);
            ApplyControlledOnInt(0,X,qp,qt[pi]);
            ApplyControlledOnInt(2^Length(qp)-1,X,qp,qt[pi]);
        }
        } apply {
            ApplyControlledOnInt(0,X,qt,y);
        }
    }    
    function getEachPeriodN(x : Qubit[],p : Int) : Qubit[] {
        if Length(x) == 0 {
            return [];
        } else {
            return [x[0]] + getEachPeriodN(x[p ...],p);
        }
    }
}