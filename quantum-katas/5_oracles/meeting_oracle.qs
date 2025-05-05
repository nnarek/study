namespace Kata {
    import Std.Convert.IntAsBoolArray;
    operation Meeting_Oracle(x : Qubit[], jasmine : Qubit[], y : Qubit)
    : Unit is Adj + Ctl {
        use qt = Qubit[Length(x)];
        within {
            for i in 0 .. Length(x)-1 {
                ApplyControlledOnBitString([false,false],X,[x[i],jasmine[i]],qt[i]);
            }
        } apply {
            ApplyControlledOnInt(0,X,qt,y);
            X(y);
        }
    }
}