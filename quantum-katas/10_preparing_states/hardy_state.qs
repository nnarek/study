namespace Kata {
    import Std.Math.ArcCos;
    open Microsoft.Quantum.Math;
    operation Hardy_State (qs : Qubit[]) : Unit {
        Ry(2.*ArcCos(Sqrt(10./12.)),qs[0]);//first qubit is |0> in 10/12 cases
        ApplyControlledOnBitString([false],Ry,[qs[0]],(2.*ArcCos(Sqrt(9./10.)),qs[1]));
        ApplyControlledOnBitString([true],H,[qs[0]],qs[1]);
    }
}
