namespace Kata {
    import Std.Arrays.*;

    operation Oracle_SATFormula(x : Qubit[], y : Qubit, formula : (Int, Bool)[][]) : Unit is Adj + Ctl {
        use cur_result = Qubit();
        use and_all = Qubit();
        X(and_all);
        for clause in formula {
            Oracle_SATClause(x,cur_result,clause);
            use temp_and_all = Qubit();
            Controlled X([cur_result,and_all],temp_and_all);
            SWAP(and_all,temp_and_all);

            Oracle_SATClause(x,cur_result,clause);
            //seems like it is impossible to deallocate temp_and_all because we have these possible states
            //temp_and_all cur_result and_all
            //0 0 0
            //0 1 0
            //1 0 0
            //1 1 1
            //but i am not sure
        }
    }

    // You might find these helper operations from earlier tasks useful.
    operation Oracle_SATClause(x : Qubit[], y : Qubit, clause : (Int, Bool)[]) : Unit is Adj + Ctl {
        let clauseQubits = Mapped((ind, _) -> x[ind], clause);
        within {
            for (ind, positive) in clause {
                if not positive {
                    X(x[ind]);
                }
            }
        } apply {
            Oracle_Or(clauseQubits, y);
        }
    }

    operation Oracle_Or(x : Qubit[], y : Qubit) : Unit is Adj + Ctl {
        ApplyControlledOnInt(0, X, x, y);
        X(y);
    }

    operation Oracle_And(x : Qubit[], y : Qubit) : Unit is Adj + Ctl {
        Controlled X(x, y);
    }
}