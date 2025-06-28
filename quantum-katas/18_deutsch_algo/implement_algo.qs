namespace Kata {
    operation DeutschAlgorithm (oracle : Qubit => Unit) : Bool {
        use arg = Qubit();
        H(arg);
        oracle(arg);
        H(arg);
        if M(arg)==Zero {
            return true;
        }
        X(arg);
        return false;
    }
}
