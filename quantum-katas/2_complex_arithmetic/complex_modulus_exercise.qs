namespace Kata {
    import Std.Math.*;

    function ComplexModulus(x : Complex) : Double {
        return Sqrt(x.Real*x.Real+x.Imag*x.Imag);
    }
}
