namespace Kata {
    import Std.Math.BitSizeI;
    operation Oracle_Majority (x : Qubit[], y : Qubit) : Unit is Adj + Ctl {
        let num_bits = BitSizeI(Length(x))+1;
        use sum = Qubit[num_bits];
        //we represent stored number as sum[0]2^0 + sum[1]2^1 + ...
        //since increment(111)=000 then we can use Adjoint to decrement and get Adjoint increment(000)=111 which is -1. Note that I first realized it in "Is Number Divisible by 3?" exercise,read it for more clearity
        //we add new bit to sum to be sure that it will not overflow when all x's are 1
        //hence first bit of sum will be 1 iff it is negative
        within {
            for i in 0 .. Length(x)-1 {
                Controlled increment([x[i]],sum);
                ApplyControlledOnInt(0,Adjoint increment,[x[i]],sum);
            }
        } apply {
            ApplyControlledOnInt(0,X,[sum[Length(sum)-1]],y);
        }
    }

    operation increment(x : Qubit[]) : Unit is Adj + Ctl {
        if Length(x)!=0 {
            X(x[0]);
            ApplyControlledOnInt(0,increment,[x[0]],x[1 ...]);
        }
    }
}
    