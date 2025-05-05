namespace Kata {
    import Std.Arrays.IndexOf;
    import Std.Convert.*;

    //O(n) mearuements without any gates
    operation SuperpositionMeasurement(qs : Qubit[], bits1 : Bool[][], bits2 : Bool[][]) : Int {
        let res = MeasureQubits(qs);
        if IndexOf(state -> res==state,bits1) != -1 {
            return 0;
        } else {
            return 1;
        }
    }
    operation MeasureQubits(qs : Qubit[]): Bool[] {
        if(Length(qs)==0) {
            return []
        } else {
            return [M(qs[0])==One] + MeasureQubits(qs[1 ...]);
        }
    }
    //trivial solution which requires one measurement but exponential number of gates in worst case 
    operation SuperpositionMeasurementTrivial(qs : Qubit[], bits1 : Bool[][], bits2 : Bool[][]) : Int {
        use qt = Qubit();
        for state in bits1 {
            ApplyControlledOnBitString(state,X,qs,qt);
        }
        //if qs is in states of bits1 then qt will have deterministic |1> state because for each basis state of qs we set 1 to qt (you can use tables to imagine what is going on) 
        return if MResetZ(qt) == One {0} else {1};
    }
}