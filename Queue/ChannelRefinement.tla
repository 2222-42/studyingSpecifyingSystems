------------------------- MODULE ChannelRefinement -------------------------
EXTENDS Sequences, Naturals

VARIABLES h, l

ErrorVal == CHOOSE v: v \notin [val: 1..12, rdy: {0, 1}, ack: {0, 1}]

BitSeqToNat[s \in Seq({0,1})] == 
    IF s = <<>> THEN 0 ELSE Head(s) + 2*BitSeqToNat[Tail(s)]

H == INSTANCE Channel WITH chan <- h, Data <- 1..12

L == INSTANCE Channel WITH chan <- l, Data <- {0,1}

------------------------- MODULE Inner -------------------------
VARIABLES bitsSent

Init == /\ bitsSent = <<>>
        /\ IF L!Init THEN  H!Init ELSE h = ErrorVal

SendBit == \E b \in {0, 1}:
                /\ L!Send(b)
                /\ IF Len(bitsSent) < 3
                    THEN 
                        /\ bitsSent' = <<b>> \o bitsSent
                        /\ UNCHANGED h
                    ELSE 
                        /\ bitsSent' = <<>>
                        /\ H!Send(BitSeqToNat[<<b>> \o bitsSent])

RcvBit ==
    /\ L!Rcv
    /\ IF bitsSent = <<>> THEN H!Rcv ELSE UNCHANGED h
    /\ UNCHANGED bitsSent

Error ==
    /\ l' # l
    /\ \neg ((\E b \in {0,1}: L!Send(b)) \/ L!Rcv)
    /\ h' = ErrorVal

Next == SendBit \/ RcvBit \/ Error
InnerIR == Init /\ [][Next]_<<l, h, bitsSent>>

InnerLiveness ==
    /\ InnerIR
    /\ \/ WF_<<l, h, bitsSent>> (RcvBit /\ (bitsSent # <<>>))
       \/ <>(h = ErrorVal)
=============================================================================
I(bitsSent) == INSTANCE Inner
IR == \EE bitsSent: I(bitsSent)!InnerIR

\* The HigherSpec should be the following:
(*
ICR(h) == INSTANCE ChannelRefinement
Liveness == \EE h, bitsSent: ICR(h)!I(bitsSent)!InnerLiveness
LSpec == \EE h: Liveness /\ IR /\ HSpec
*)
=============================================================================
\* Modification History
\* Created Tue Apr 14 20:51:45 JST 2020 by daioh
