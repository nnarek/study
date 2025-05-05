namespace Kata {
    import Std.Arrays.Mapped;
    operation Oracle_SATClause(x : Qubit[], y : Qubit, clause : (Int, Bool)[]) : Unit is Adj + Ctl {
        within {
            for var in clause {
                let (index,keep) = var;
                if keep == false {
                    X(x[index]);
                }
            } 
        } apply {
            Oracle_Or(Mapped((i,b) -> x[i],clause),y);
        }
    }

    // You might find this helper operation from an earlier task useful.
    operation Oracle_Or(x : Qubit[], y : Qubit) : Unit is Adj + Ctl {
        ApplyControlledOnInt(0, X, x, y);
        X(y);
    }        
}
