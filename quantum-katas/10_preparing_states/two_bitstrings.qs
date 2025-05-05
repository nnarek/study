namespace Kata {

    function FirstMismatchIndex(a : Bool[], b : Bool[]) : Int {
        for i in 0 .. Length(a) - 1 {
            if (a[i] != b[i]) {
                return i;
            }
        }
        return -1;
    }

    operation TwoBitstringSuperposition (qs : Qubit[], bits1 : Bool[], bits2 : Bool[]) : Unit is Adj + Ctl {
        // we can not use mutable here because autogenerator of Adj and Ctl of Q# not able to find inverse of this operation
        let mis = FirstMismatchIndex(bits1,bits2);
        H(qs[mis]);
        for i in 0 .. Length(qs) - 1 {
            if(i!=mis){
                if(bits1[i]){
                    ApplyControlledOnBitString([bits1[mis]],X,[qs[mis]],qs[i]);
                }
                if(bits2[i]){
                    ApplyControlledOnBitString([bits2[mis]],X,[qs[mis]],qs[i]);
                }
            }
        }
    }    
//second solution which I found by looking few parts of solution
operation TwoBitstringSuperposition_ (qs : Qubit[], bits1 : Bool[], bits2 : Bool[]) : Unit is Adj + Ctl {
        use q = Qubit();
        H(q);
        for i in 0 .. Length(qs) - 1 {
            if(bits1[i]){
                ApplyControlledOnBitString([false],X,[q],qs[i]);
            }
            if(bits2[i]){
                ApplyControlledOnBitString([true],X,[q],qs[i]);
            }
        }
        //now q qubit should have |0> state. and it have only |1> state if qs is in state bits2
        //we need to switch it back only for that state
        ApplyControlledOnBitString(bits2,X,qs,q);
    }
}    
