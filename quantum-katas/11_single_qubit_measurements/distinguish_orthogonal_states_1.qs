namespace Kata {
    import Std.Math.*;

    operation IsQubitPsiPlus(q : Qubit) : Bool {
        // if we will measure this qubit in basis of |psi_+> and |psi_-> then we can deterministically determine in which state is 'q' Qubit
        // so we need to apply |0><psi_+| + |1><psi_-| operator to input Qubit q to replace its |psi_+> |psi_-> basis vectors to PauliZ basis vectors, leaving amplitudes same
        // above operator is same as inverse of |psi_+><0| + |psi_-><1| operator, which is Ry(2*arctan(0.8,0.6))
        Ry(-2.0*ArcTan2(0.8,0.6),q);
        let res = M(q);
        if res == Zero {
            return true;
        } else {
            return false;
        }
    }
}