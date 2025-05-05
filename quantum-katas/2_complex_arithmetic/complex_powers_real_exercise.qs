namespace Kata {
    import Std.Math.*;

    function ComplexExpReal(r : Double, x : Complex) : Complex {
        let (a,b) = (x.Real,x.Imag);
        if(r == 0.){
            return Complex(0., 0.);
        }
        return Complex(r^a*Cos(Log(r)*b), r^a*Sin(Log(r)*b));

    }
}