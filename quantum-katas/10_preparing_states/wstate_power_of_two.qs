namespace Kata {
    import Std.Math.Round;
    import Std.Math.Log;
    import Std.Convert.*;
    import Std.Math.LogOf2;
    open Microsoft.Quantum.Convert;
    operation WState_PowerOfTwo (qs : Qubit[]) : Unit {
        //trying to solve without rotation gates
        use qh = Qubit[Round(Log(IntAsDouble(Length(qs)))/LogOf2())];
        Message($"The length is: {Length(qh)}");
        for i in 0 .. Length(qh)-1 {
            H(qh[i]);
        }
        for i in 0 .. Length(qs)-1 {
            ApplyControlledOnInt(i,X,qh,qs[i]);
        }
        //ResetAll(qh);
        //TODO why reset does not work
        for iqs in 0 .. Length(qs)-1 {
            let bits = IntAsBoolArray(iqs,Length(qh));
            for iqh in 0 .. Length(qh)-1 {
                if bits[iqh]{
                    ApplyControlledOnInt(1,X,[qs[iqs]],qh[iqh]);
                }
            }
        }
    }
}
