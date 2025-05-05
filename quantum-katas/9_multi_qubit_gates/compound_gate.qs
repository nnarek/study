namespace Kata {
    operation CompoundGate(qs : Qubit[]) : Unit is Adj + Ctl {
        //diagonal matrices of Q is Y Y ZX ZX
        //also top left 4x4 matrix is same as bottom right but multiplied by i
        //hence we need to multiply some matrix with TopLeft(top left 4x4 matrix) so that top left is 1 and bottom right is i
        //such matrix is S. hence we have Q=S*TopLeft, where top left can be splitted into I(identity matrix) and Y
        //finally we have Q=S*I*Y

        S(qs[0]);
        Y(qs[2]);
    }
}