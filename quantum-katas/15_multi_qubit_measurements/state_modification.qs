namespace Kata {
    operation StateSelection(qs : Qubit[], ind : Int) : Unit {
        ApplyControlledOnInt(1-ind,X,[qs[0]],qs[1]);
    }
}