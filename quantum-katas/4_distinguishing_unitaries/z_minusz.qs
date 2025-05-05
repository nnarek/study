namespace Kata {
    operation DistinguishZfromMinusZ (unitary : (Qubit => Unit is Adj + Ctl)) : Int {
        // Z|phi> and -Z|phi> aleays have 180 degree angle and they are not orthogonal
        // if we will have some intial state and apply operators before and after unitary operator then we will have two AZB|phi> or -AZB|phi> possible states and they never can be orthogonal
        // inverse of Z and -Z are also same
        // we can try to apply controlled variants to apply one of them and not another, but befote that we need to get different states which i think is impossible  
        
        
        
        return -1;
    }
}
