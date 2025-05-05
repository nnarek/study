namespace Kata {
    import Std.Arrays.Fold;
    import Std.Arrays.Mapped;
    import Std.Convert.*;
    function findMismatchPosition(bits1 : Bool[][], bits2 : Bool[][]) : Int {
        for pos in 0 .. Length(bits1[0])-1 {
            let column1 = Mapped(state -> state[pos],bits1);
            let column2 = Mapped(state -> state[pos],bits2);
            let all_equal1 = Fold((res,b) -> res and column1[0]==b,true,column1);
            let all_equal2 = Fold((res,b) -> res and column2[0]==b,true,column2);
            if all_equal1 and all_equal2 and column1[0]!=column2[0] {
                return pos;
            }
        }
        return -1;
    }
    operation SuperpositionOneMeasurement(qs : Qubit[], bits1 : Bool[][], bits2 : Bool[][]) : Int {
        let mis_pos = findMismatchPosition(bits1,bits2);
        let result = MResetZ(qs[mis_pos]) == One;
        if result == bits1[0][mis_pos] {
            return 0
        } else {
            return 1
        }
    }
}