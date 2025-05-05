namespace Kata {
    import Std.Convert.ResultAsBool;
    operation IsQubitOne (q : Qubit) : Bool {
        return ResultAsBool(M(q));
    }
}