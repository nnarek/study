namespace Kata {
    import Std.Math.PI;
    operation IsQubitZeroOrPlus (q : Qubit) : Bool {
        // since we will get |0> or |+> with equal probability then we can just measure qubit in pauliZ and get 1 in 0.25 cases(in this case we need to answer false and we will always be right) or get 0 in 0.75 cases(in this case we answer true to maximize right answers and we will be right in 0.5 cases)
        // so overall accuracy will be 0.75 for above solution

        //we can apply H and |0> will be transformed to |+> and |+> will be transformed to |0>, so we will have same problem

        //lets try to find best transofmration which will allow as to distinguesh this states with high probability 
        //we need to apply some optimal operator U which will transform U|0>=x|0>+sqrt(1-x^2)|1> where x is some real number which should be optimized
        //also let assume that operation U will transform U|1>=y|0>+sqrt(1-y^2)|1>
        //in 0.5 cases we will have |0> and after that we will measure 0 in 0.5*x^2 of overall cases and will measure 1 in 0.5*(1-x^2) of overall cases
        //in 0.5 cases we will have |+> and after measurement we will get 0 in 0.5*((x+y)^2/2) of overall cases and 1 in 0.5*(1-(x+y)^2/2) cases
        //so if we will measure and get 0 then we need to choose maximum from 0.5*x^2 and 0.5*((x+y)^2/2) probabilites to maximize accuracy 
        //to maximize accuracy if we get 1, we need to choose maximum from 0.5*(1-x^2) and 0.5*(1-(x+y)^2/2)
        //hence overall accuracy will get max(0.5*x^2 , 0.5*((x+y)^2/2)) + max(0.5*(1-x^2) , 0.5*(1-(x+y)^2/2)
        //after getting wrong results I realized that y can not be arbitrary and it have some dependency from x
        //so I choosed Ry operator and if Ry(p)|0>=x|0>+sqrt(1-x^2)|1> then Ry(p)|1>=-sqrt(1-x^2)|0>+x|1>
        //in this case we will have this optimization problem 
        //Maximize[max(0.5*x^2 , 0.5*((x-sqrt(1-x^2))^2/2)) + max(0.5*(1-x^2) , 0.5*(1-(x-sqrt(1-x^2))^2/2))  ,{x,0,1}]
        //which return that accuracy is optimal at x=sqrt(2+sqrt(2))/2 = 0.92388 point with 1/4(2+sqrt(2)) = 0.85355 
        //so angle p of Ry is equal to 2*arctan2(sqrt(1-(sqrt(2+sqrt(2))/2)**2),sqrt(2+sqrt(2))/2) = pi/4
        //because 0.5*x^2 > 0.5*((x-sqrt(1-x^2))^2/2) we need to choose |0> if measurement returned 0 and return |+> otherwise
        //TODO try to prove that this is best solution, look into solutions if needed
        //TODO add generic solution into notes

        Ry(PI()/4.,q);
        if M(q) == Zero {
            return true;
        } else {
            return false;
        }
    }
}