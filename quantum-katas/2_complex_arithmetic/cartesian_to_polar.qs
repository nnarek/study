namespace Kata {
    import Std.Math.*;

    function ComplexToComplexPolar(x : Complex) : ComplexPolar {
        let (a,b) = (x.Real,x.Imag);
        let modX = Sqrt(a^2.+b^2.);
        return ComplexPolar(modX, ArcTan2(b,a));
    }
}