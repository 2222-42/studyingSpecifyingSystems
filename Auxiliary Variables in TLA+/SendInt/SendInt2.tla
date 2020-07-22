------------------------------ MODULE SendInt2 ------------------------------
EXTENDS Integers

NotInt == CHOOSE n: n \notin Int

VARIABLES x, z

Init == /\ x = NotInt
        /\ z \in Int

Send == /\ x = NotInt
        /\ x' = z
        /\ z' = NotInt

Rcv == /\ x \in Int
       /\ x' = NotInt
       /\ z' \in Int

Next == Send \/ Rcv

Spec == Init /\ [][Next]_<<x,z>>
=============================================================================
\* Modification History
\* Created Fri Jul 17 14:54:26 JST 2020 by daioh
