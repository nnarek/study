namespace Kata {
    operation Oracle_ContainsSubstring (x : Qubit[], y : Qubit, r : Bool[]) : Unit is Adj + Ctl {
        use qt = Qubit[Length(x)-Length(r)+1];//TODO same as official solutiion, but try to find better way(at least for true,true pattern)
        within {
            for i in 0 .. Length(x)-Length(r) {
                Oracle_ContainsSubstringAtPosition(x,qt[i],r,i);
            }
        } apply {
            ApplyControlledOnInt(0,X,qt,y);
            X(y);
        }
    }  

    // You might find this helper operation from an earlier task useful.  
    operation Oracle_ContainsSubstringAtPosition (x : Qubit[], y : Qubit, r : Bool[], p : Int) : Unit is Adj + Ctl {
        ApplyControlledOnBitString(r, X, x[p .. p + Length(r) - 1], y);
    }     
}