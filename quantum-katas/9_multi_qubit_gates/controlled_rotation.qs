namespace Kata {
    operation ControlledRotation(qs : Qubit[], theta : Double)
    : Unit is Adj + Ctl {
        Controlled Rx([qs[0]],(theta,qs[1]));
    }
}