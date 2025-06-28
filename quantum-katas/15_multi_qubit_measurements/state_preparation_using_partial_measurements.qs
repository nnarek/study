namespace Kata {
    operation PostSelection(qs : Qubit[]) : Unit {
        ApplyToEachA(H,qs);
        use qt = Qubit();
        Controlled X(qs,qt);
        if M(qt) == One {//used rejection samping
            ApplyToEachA(X,qs);
            PostSelection(qs);
        }
    }
}