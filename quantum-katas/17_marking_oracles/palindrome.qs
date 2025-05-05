namespace Kata {
    operation Oracle_Palindrome (x : Qubit[], y : Qubit) : Unit is Adj + Ctl {
        within {
            for i in 0 .. Length(x)/2-1 {
                ApplyControlledOnBitString([true],X,[x[Length(x)-1-i]],x[i]);//if "i" and "len-1-i" are equal then left side will be 0
            }
        } apply {
            ApplyControlledOnInt(0,X,x[0 .. Length(x)/2-1],y);
        }
    }    

    operation Oracle_Palindrome_auxQubits (x : Qubit[], y : Qubit) : Unit is Adj + Ctl {
        if Length(x) >= 2 {
            use qt = Qubit[Length(x)/2];
            within {
                for i in 0 .. Length(x)/2-1 {
                    X(qt[i]);
                    ApplyControlledOnBitString([false,false],X,[x[i],x[Length(x)-1-i]],qt[i]);
                    ApplyControlledOnBitString([true,true],X,[x[i],x[Length(x)-1-i]],qt[i]);
                }
            } apply {
                ApplyControlledOnInt(0,X,qt,y);
            }
        }
    }    
}
