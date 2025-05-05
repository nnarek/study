namespace Kata {
    open Microsoft.Quantum.Math;
    operation ThreeStates_TwoQubits (qs : Qubit[]) : Unit is Adj + Ctl {
        //we can apply some gate to make first qubit superpositioned with (2/3 1/3) frequencies
        //after that we can conditionally apply H if first qubit is 0
        let value = Sqrt(2.0 / 3.0);
        let angle = ArcCos(value);
        Ry(angle*2.,qs[0]);
        ApplyControlledOnBitString([false],H,[qs[0]],qs[1]);
        //TODO understand official solution
    }  
}

