namespace Kata {
    operation Oracle_DivisibleBy3 (x : Qubit[], y : Qubit) : Unit is Adj + Ctl {
        //if we have number b0*2^0 + b1*2^1 + b2*2^2 + ...
        //then mod3 equivalent of that number will be b0*1 + b1*2 + b2*1 + b3*2 + b4*1 + ... 
        //because 2^n mod3 gives 1,2,1,2,1,2 periodic results
        //hence we can increament and in next iteration increment two time and repeat periodically
        //if final sum %3 is 0 then number devides to 3
        use qstate3 = Qubit[2];
        within {
            for i in 0 .. Length(x)-1 {
                Controlled increament_mod3([x[i]],qstate3);
                if i%2==1 {
                    Controlled increament_mod3([x[i]],qstate3);
                } 
                //looking to solutions I notice that above code is same as following
                //because -1=2 by mod3 and we can just decrement counter
                //and inverse of increament operator is decrement because instead of doing 0->1,1->2,2->0 its perform 1->0,2->1,0->2  
                //if i % 2 == 0 {
                //    Controlled IncrementMod3([x[i]], counter);
                //} else {
                //    Controlled Adjoint IncrementMod3([x[i]], counter);
                //}
            }
        } apply {
            ApplyControlledOnInt(0,X,qstate3,y);
        }
    }

    operation increament_mod3 (c : Qubit[]) : Unit is Adj + Ctl {
        ApplyControlledOnBitString([false],X,[c[0]],c[1]);
        ApplyControlledOnBitString([false],X,[c[1]],c[0]);
    }
}