-------------------------- MODULE AsynchInterface --------------------------

EXTENDS Naturals

CONSTANT Data

VARIABLES val, rdy, ack

TypeInvariant == 
    /\ val \in Data
    /\ rdy \in {0, 1}
    /\ ack \in {0, 1}

--------------------------------------------------------------

Init == 
    /\ val \in Data
    /\ rdy \in {0, 1}
    /\ ack = rdy

Send ==
    /\ rdy = ack
    /\ val' \in Data
    /\ rdy' = 1 - rdy
    /\ UNCHANGED ack

Rcv ==
    /\ rdy /= ack
    /\ ack' = 1 - ack
    /\ UNCHANGED <<val, rdy>>

Next == 
    \/ Send
    \/ Rcv

Spec == Init /\ [][Next]_<<val, rdy, ack>>

(*
I don't know how to should write the code to compare the different specs.
-------------------------------------------------------------------------
C(chan) == INSTANCE Cahnnel 
AIEq == Spec <=> \EE chan: (C(chan)![](chan = [val |-> val, rdy |-> rdy, ack |-> ack]) /\ C(chan)!Spec)
-------------------------------------------------------------------------
*)
--------------------------------------------------------------

THEOREM Spec => []TypeInvariant

=============================================================================
\* Modification History
\* Last modified Sat Apr 18 13:23:53 JST 2020 by daioh
\* Created Sat Jan 18 06:47:43 JST 2020 by daioh
