namespace Kata {
 operation ApplyMarkingOracleAsPhaseOracle(
        markingOracle : (Qubit[], Qubit) => Unit is Adj + Ctl,
        qubits : Qubit[])
    : Unit is Adj + Ctl {
        use qtemp = Qubit();
        X(qtemp);
        H(qtemp);
        markingOracle(qubits,qtemp);
        H(qtemp);
        X(qtemp);
    }
    operation ApplyMarkingOracleAsPhaseOracle_without_kickback(
        markingOracle : (Qubit[], Qubit) => Unit is Adj + Ctl,
        qubits : Qubit[])
    : Unit is Adj + Ctl {
        use qtemp = Qubit();
        markingOracle(qubits,qtemp);
        
        Controlled Z([qtemp],qubits[0]);//flipping sign for qubits[0] which have 1 state
        
        Controlled X([qtemp],qubits[0]);//flipping qubits[0] to be able to flip sign for qubits[0] which have 0 state,later we will flip back
        Controlled Z([qtemp],qubits[0]);
        Controlled X([qtemp],qubits[0]);
        
        markingOracle(qubits,qtemp);//deallication
    }
}