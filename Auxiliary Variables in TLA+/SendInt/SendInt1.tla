------------------------------ MODULE SendInt1 ------------------------------
EXTENDS Integers

NotInt == CHOOSE n: n \notin Int

VARIABLES x

Init == /\ x = NotInt

Send == /\ x = NotInt
        /\ x' \in Int

Rcv == /\ x \in Int
       /\ x' = NotInt

Next == Send \/ Rcv

Spec == Init /\ [][Next]_x

=============================================================================
\* Modification History
\* Created Fri Jul 17 14:53:47 JST 2020 by daioh
