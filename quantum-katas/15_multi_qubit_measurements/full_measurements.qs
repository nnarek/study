namespace Kata {
    import Std.Convert.ResultAsBool;
    operation BasisStateMeasurement(qs : Qubit[]) : Int {
        let r0 = if M(qs[0]) == Zero { 0 } else { 1 };
        let r1 = if M(qs[1]) == Zero { 0 } else { 1 };
        return 2*r0 + r1;
    }
}