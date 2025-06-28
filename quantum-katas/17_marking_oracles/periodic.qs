namespace Kata {
    operation Oracle_Periodic (x : Qubit[], y : Qubit) : Unit is Adj + Ctl {
        // if we have string x with length N then
        // it will have periodicity N-1 if x[0]==x[N-1]
        // it will have periodicity N-2 if x[0]==x[N-2] and x[1]==x[N-1]
        // and so on until periodicity N/2
        // if we will check periodicities from N/2 to N-1 and find out that there is no one which is periodic 
        // then there is no need to check peridoicites from 0 to N/2 because all of them can be multiplied by 2 to get number some number between N/2 .. N-1(and hence they are sub periods and no need to check them)
        let N = Length(x);
        use pt = Qubit[N/2+1];
        within {
            for p in  N/2 .. N-1 {
                Oracle_PeriodicGivenPeriod (x, pt[p-N/2], p);
            }
        } apply {
            ApplyControlledOnInt(0, X, pt, y);
            X(y);
        }
    }

    // You might find this helper operation from an earlier task useful.
    operation Oracle_PeriodicGivenPeriod (x : Qubit[], y : Qubit, p : Int) : Unit is Adj + Ctl {
        let n = Length(x);
        within {
            for i in 0 .. n - p - 1 {
                CNOT(x[i + p], x[i]);
            }
        } apply {
            ApplyControlledOnInt(0, X, x[... n - p - 1], y);
        }
    }    
}
