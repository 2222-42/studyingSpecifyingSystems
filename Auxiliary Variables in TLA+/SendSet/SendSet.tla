------------------------------ MODULE SendSet ------------------------------
CONSTANT Data

NonData == CHOOSE d : d \notin Data

VARIABLES x, y
vars == <<x,y>>

Init == (x = NonData) /\ (y = {})

Choose == /\ \E d \in Data \ y : y' = y \cup {d}
          /\ x' = x

Send == /\ x = NonData
        /\ x' \in y
        /\ y' = y \ {x'}

Rcv == /\ x \in Data
       /\ x' = NonData
       /\ y' = y

Next == Choose \/ Send \/ Rcv

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Created Sun Jul 26 17:06:06 JST 2020 by daioh
