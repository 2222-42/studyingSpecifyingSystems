------------------------------ MODULE SendSeq ------------------------------
EXTENDS Sequences, Integers

CONSTANT Data

NonData == CHOOSE v: v \notin Data

VARIABLES x, y
vars == <<x,y>>

Init == (x = NonData) /\ (y = <<>>)

Choose == /\ \E d \in Data : y' = Append(y, d)
          /\ x' = x

Send == /\ x = NonData /\ y # <<>>
        /\ x' = Head(y)
        /\ y' = Tail(y)

Rcv == /\ x \in Data
       /\ x' = NonData
       /\ y' = y

Next == Choose \/ Send \/ Rcv

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Created Wed Jul 29 09:47:50 JST 2020 by daioh
