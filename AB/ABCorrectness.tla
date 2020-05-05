--------------------------- MODULE ABCorrectness ---------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLES sBit, sAck, sent, rcvd, rBit
-----------------------------------------------------------------------------
ABCInit == /\ sBit \in {0, 1}
           /\ sAck = sBit
           /\ rBit = sBit
           /\ sent \in Data
           /\ rcvd \in Data

CSndNewValue(d) == /\ sAck = sBit
                   /\ sBit' = 1 - sBit
                   /\ sent' = d
                   /\ UNCHANGED <<sAck, rBit, rcvd>>

CRcvMsg ==
    /\ rBit # sBit
    /\ rBit' = sBit
    /\ rcvd' = sent
    /\ UNCHANGED <<sBit, sAck, sent>>

CRcvAck ==
    /\ rBit # sAck
    /\ sAck' = rBit
    /\ UNCHANGED <<sBit, rBit, sent, rcvd>>

ABCNext == \/ \E d \in Data : CSndNewValue(d)
           \/ CRcvMsg \/ CRcvAck

-----------------------------------------------------------------------------
cvars == <<sBit, sAck, sent, rcvd, rBit>>
ABCFairness == WF_cvars(CRcvMsg) /\ WF_cvars(CRcvAck)

ABCSpec == ABCInit /\ [][ABCNext]_cvars /\ ABCFairness
=============================================================================
\* Modification History
\* Created Tue May 05 14:53:31 JST 2020 by daioh
