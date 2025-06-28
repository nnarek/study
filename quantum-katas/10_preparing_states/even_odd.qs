namespace Kata {
    operation EvenOddNumbersSuperposition(qs : Qubit[], isEven : Bool) : Unit is Adj + Ctl {
        for i in 0 .. Length(qs) - 2 {
            H(qs[i]);
        }
        if(isEven == false){
            X(qs[Length(qs)-1]);
        }
    }
}

