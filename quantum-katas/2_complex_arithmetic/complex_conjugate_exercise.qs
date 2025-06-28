namespace Kata {
    import Std.Math.*;

    function ComplexConjugate(x : Complex) : Complex {
        let (a, b) = (x.Real, x.Imag);
        return Complex(a, -b);
    }
}