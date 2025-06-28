namespace Kata {
    import Std.Arrays.*;

    operation GHZ_State(qs : Qubit[]) : Unit is Adj + Ctl {
        H(qs[0]);
        for i in 1 .. Length(qs) - 1 {
            CNOT(qs[0],qs[i]);
        }
    }
}