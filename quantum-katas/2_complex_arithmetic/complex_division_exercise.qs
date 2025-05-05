namespace Kata {
    import Std.Math.*;

    function ComplexDiv(x : Complex, y : Complex) : Complex {
        let (a,b) = (x.Real,x.Imag);
        let (c,d) = (y.Real,y.Imag);
        let sq = c*c+d*d;
        return Complex((a*c+b*d)/sq, (b*c-a*d)/sq);
    }
}