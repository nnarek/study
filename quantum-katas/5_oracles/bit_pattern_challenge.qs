namespace Kata {


    operation ArbitraryBitPattern_Oracle_Challenge_auxQubit_kickback(x : Qubit[], pattern : Bool[])
    : Unit is Adj + Ctl {
        //TODO solve without temporary qubit
        use q = Qubit();
        within {
            X(q);
            H(q);
        } apply {
            ApplyControlledOnBitString(pattern,X,x,q);
        }

    }

    operation ArbitraryBitPattern_Oracle_Challenge_auxQubit(x : Qubit[], pattern : Bool[])
        : Unit is Adj + Ctl {
        //first I have solved with temporary qubit and without kickbacking 
        use q = Qubit();
        let first_true = FirstTrue(pattern);
        if first_true == -1 {
            ApplyControlledOnBitString(pattern,X,x,q);
            ApplyControlledOnBitString([true],X,[q],x[0]);
            ApplyControlledOnBitString([true],Z,[q],x[0]);
            ApplyControlledOnBitString([true],X,[q],x[0]);
            ApplyControlledOnBitString(pattern,X,x,q);
        } else {
            ApplyControlledOnBitString(pattern,X,x,q);
            ApplyControlledOnBitString([true],Z,[q],x[first_true]);
            ApplyControlledOnBitString(pattern,X,x,q);
        }
    }

    function FirstTrue(pattern : Bool[]) : Int {
        for i in 0 .. Length(pattern)-1 {
            if pattern[i] {
                return i;
            }
        }
        return -1;
    }
}