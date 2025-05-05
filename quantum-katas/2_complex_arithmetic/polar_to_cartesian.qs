namespace Kata {
    import Std.Math.*;

    function ComplexPolarToComplex(x : ComplexPolar) : Complex {
        return Complex(x.Magnitude*Cos(x.Argument), x.Magnitude*Sin(x.Argument));
    }
}
