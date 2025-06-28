namespace Kata {
    operation Oracle_ContainsSubstringAtPosition (x : Qubit[], y : Qubit, r : Bool[], p : Int) : Unit is Adj + Ctl {
        //task ask to check exect match only for exact place, it does not ask to find any match in one of places 
        ApplyControlledOnBitString(r,X,x[p .. p+Length(r)-1],y);
    }    
}
