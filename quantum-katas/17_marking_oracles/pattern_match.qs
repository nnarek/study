namespace Kata {
    import Std.Arrays.*;

    operation Oracle_PatternMatching(x : Qubit[], y : Qubit, a : Int[], r : Bool[]) : Unit is Adj + Ctl {
        ApplyControlledOnBitString(r,X,Mapped(index -> x[index],a),y);
    }
}