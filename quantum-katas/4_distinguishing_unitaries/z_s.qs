namespace Kata {
    operation DistinguishZfromS(unitary : (Qubit => Unit is Adj + Ctl)) : Int {
        //we can try to find some state |phi> so that Z|phi> and S|phi> are orthogonal, so we will able to distinguesh two states by one measurement
        //but there is no such |phi> because dot product of final vectors are (S|phi>)^+ (Z|phi>)=(r1(pi/2)|phi>)^+ r1(pi)|phi> = |phi>^+ (r1(pi/2)^+ r1(pi)) |phi> = |phi>^+ r1(pi/2) |phi> = <phi|S|phi>
        //if |phi> = [a+bi c+di]^T then <phi| = [a-bi c-di] and <phi|S|phi> = <phi|[a+bi -d+ci]^T = [a-bi c-di][a+bi -d+ci]^T = a^2+b^2+i(c^2+d^2) which is 0 only when a=b=c=d=0, this mean that there is no valid initial state |phi>

        //then i noticed that SS=Z and ZZ=I, so we can apply this operation twice and we will have same problem as distinguishing Z and I which is solved previously

        use qt = Qubit();
        H(qt);//we have |+> state
        unitary(qt);
        unitary(qt);
        if Measure([PauliX],[qt])==One {//state was changed to |->
            Z(qt);
            H(qt);
            return 1;
        } else {
            H(qt);
            return 0;
        }
    }
}