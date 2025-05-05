namespace Kata {
    import Std.Math.BitSizeI;
    operation Oracle_Balanced (x : Qubit[], y : Qubit) : Unit is Adj + Ctl {
        let num_bits = BitSizeI(Length(x));
        use sum = Qubit[num_bits];
        //we represent stored number as sum[0]2^0 + sum[1]2^1 + ...

        within {
            for i in 0 .. Length(x)-1 {
                Controlled increment([x[i]],sum);
            }
        } apply {
            ApplyControlledOnInt(Length(x)/2,X,sum,y);
        }
    }

    operation increment(x : Qubit[]) : Unit is Adj + Ctl {
        if Length(x)!=0 {
            X(x[0]);
            ApplyControlledOnInt(0,increment,[x[0]],x[1 ...]);
        }
    }

    operation increment_wrong(x : Qubit[]) : Unit is Adj + Ctl {
        use qtemp = Qubit();
        // we need to check whether we have 0 01 011 0111 at the beggining of array and repace them by 1 10 100 1000
        for i in Length(x)-1 .. -1 .. 0 {
            //when I iterate from end to begin then we replace 0111 by 1000 then at final iteration, 0 pattern also will be matched
            //same can happen if we will iterate in right order 
            ApplyControlledOnInt(2^i-1,X,x[Length(x)-1-i ...],qtemp);
            for k in Length(x)-1-i .. Length(x)-1 {
                CNOT(qtemp,x[k]);
            }
            ApplyControlledOnInt(2^i,X,x[Length(x)-1-i ...],qtemp);//reversing qtemp back,can not use "within-apply" because in that case we can not change x during apply
        }
        //then I realized that recursive solution is way easy
    }
}
