-------------------------- MODULE MCAlternatingBit --------------------------
EXTENDS AlternatingBit

INSTANCE ABCorrectness

CONSTANT msgQLen, ackQLen

SeqConstant == /\ Len(msgQ) <= msgQLen
               /\ Len(ackQ) <= ackQLen

SentLeadsToRcvd ==
    \A d \in Data : (sent = d) /\ (sBit # sAck) ~> (rcvd = d)

\* AB(h) == INSTANCE ABCorrectness
\* THEOREM ABSpec => \EE h : AB(h)!ABCSpec
\*oh == Data
\*ABCSpecBar == AB(oh)!ABCSpec
\*
\*THEOREM ABSpec => ABCSpecBar
=============================================================================
\* Modification History
\* Last modified Tue May 05 15:13:35 JST 2020 by daioh
\* Created Tue May 05 06:31:05 JST 2020 by daioh
