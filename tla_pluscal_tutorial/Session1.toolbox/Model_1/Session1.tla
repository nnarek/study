------------------------------ MODULE Session1 ------------------------------
EXTENDS Integers

IsPrime(n) ==    (n > 1)  
              /\ \A m \in 2..(n-1) : ~ \E p \in 2..(n-1) : n = m * p 

IsEven(n) == (\E d \in Int : n = 2 * d) \* (\E d \in Int : n = 2 * d) can not be bound checked

GoldbachCconjecture == \A n \in Int : (2 < n) /\ IsEven(n) /\ \E p1,p2 \in Int : IsPrime(p1) /\ IsPrime(p2) /\ p1+p2=n

=============================================================================
\* Modification History
\* Last modified Wed Mar 19 21:06:34 GET 2025 by developer
\* Last modified Thu Dec 17 15:34:55 PST 2020 by lamport
\* Created Sat Dec 05 17:41:14 PST 2020 by lamport
