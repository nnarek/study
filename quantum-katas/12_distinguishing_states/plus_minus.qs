namespace Kata {
    import Std.Convert.ResultAsBool;
    operation IsQubitPlus(q : Qubit) : Bool {
        return Measure([PauliX],[q])==Zero;
    }
}
