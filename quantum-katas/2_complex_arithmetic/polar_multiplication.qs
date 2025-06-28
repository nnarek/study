namespace Kata {
    import Std.Math.*;

    function ComplexPolarMult(x : ComplexPolar, y : ComplexPolar) : ComplexPolar {
        let newMag = x.Magnitude*y.Magnitude;
        let newArg = x.Argument+y.Argument;
        if(PI() < newArg) {
            return ComplexPolar(newMag,newArg - 2.*PI());
        } else {
            if(newArg < -PI() ){
                return ComplexPolar(newMag,newArg + 2.*PI());
            } else {//sum of both can not exceed 2*Pi, so no need to calculate newArg%(2*PI)
                return ComplexPolar(newMag,newArg);
            }
        }
        
    }
}