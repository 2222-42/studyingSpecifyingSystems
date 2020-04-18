------------------------------ MODULE Channel ------------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLES chan

TypeInvariant == 
    chan \in [val: Data, rdy: {0, 1}, ack: {0, 1}]

--------------------------------------------------------------

Init == 
    /\ TypeInvariant
    /\ chan.ack = chan.rdy

Send(d) ==
    /\ chan.rdy = chan.ack
    /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

Rcv ==
    /\ chan.rdy /= chan.ack
    /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next == 
    \/ (\E d \in Data: Send(d))
    \/ Rcv

\* WF_chan (Rcv)
\* []([] ENABLED <<Rcv>>_chan => <><<Rcv>>_chan)

Spec == Init /\ [][Next]_chan
\* Spec == Init /\ WF_chan (Rcv)

(*
I don't know how to should write the code to compare the different specs.
-------------------------------------------------------------------------
AI == INSTANCE AsynchInterface WITH val <- chan.val, rdy <- chan.rdy, ack <- chan.ack 

GoodVals == 
    /\ AI!val = chan.val
    /\ AI!rdy = chan.rdy
    /\ AI!ack = chan.ack

BadVals ==
    \/ val # chan.val
    \/ rdy # chan.rdy
    \/ ack # chan.ack

P == IF chan \in [val: Data, rdy: {0, 1}, ack: {0, 1}] THEN GoodVals
                                                       ELSE BadVals

ChannelEq == ([]P /\ AI!Spec) <=> Spec
-------------------------------------------------------------------------
*)
--------------------------------------------------------------

THEOREM Spec => []TypeInvariant

=============================================================================
\* Modification History
\* Last modified Sat Apr 18 13:17:49 JST 2020 by daioh
\* Created Fri Jan 24 02:45:46 JST 2020 by daioh
