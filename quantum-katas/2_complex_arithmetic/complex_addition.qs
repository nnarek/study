namespace Kata {
    import Std.Math.*;

    function ComplexAdd(x : Complex, y : Complex) : Complex {
        // Extract real and imaginary components of the inputs.
        let (a, b) = (x.Real, x.Imag);
        let (c, d) = (y.Real, y.Imag);
        return Complex(a+c, b+d);
    }
}