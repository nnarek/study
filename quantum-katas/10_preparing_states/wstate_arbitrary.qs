namespace Kata {
    import Std.Math.Sqrt;
    import Std.Math.ArcCos;
    import Std.Convert.IntAsDouble;
    operation WState_Arbitrary (qs : Qubit[]) : Unit is Adj + Ctl {
        // first qubit should have (N-1)/N and 1/N frequencies for |0> and |1> states
        // if first qubit is 1 then others should be 0
        // if first qubit is 0 then others should have W state and we can apply operator recursivelly to get that state
        if(Length(qs)==1){
            X(qs[0]);
        } else {
            Ry(2.*ArcCos(Sqrt(1.-1./IntAsDouble(Length(qs)))),qs[0]);
            ApplyControlledOnBitString([false],WState_Arbitrary,[qs[0]],qs[1...]);
            //no need to set others 0 if qs[0]==true because they are already 0
        }
    }
}
