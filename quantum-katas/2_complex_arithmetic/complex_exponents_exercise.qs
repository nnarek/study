namespace Kata {
    import Std.Math.*;

    function ComplexExponent(x : Complex) : Complex {
        let (a,b) = (x.Real,x.Imag);
        return Complex(E()^a*Cos(b), E()^a*Sin(b));
    }
}