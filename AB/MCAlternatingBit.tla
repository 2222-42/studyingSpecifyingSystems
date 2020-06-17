-------------------------- MODULE MCAlternatingBit --------------------------
EXTENDS AlternatingBit

INSTANCE ABCorrectness

CONSTANT msgQLen, ackQLen

SeqConstraint == /\ Len(msgQ) <= msgQLen
               /\ Len(ackQ) <= ackQLen

SentLeadsToRcvd ==
    \A d \in Data : (sent = d) /\ (sBit # sAck) ~> (rcvd = d)

\* AB(h) == INSTANCE ABCorrectness
\* THEOREM ABSpec => \EE h : AB(h)!ABCSpec
(* I am not sure how to make state function `oh`  *)
\*oh == Data
\*ABCSpecBar == AB(oh)!ABCSpec
\*
\*THEOREM ABSpec => ABCSpecBar
\*

(* the followings are cpied from tlaplus/Examples *)
ImpliedAction == [ABCNext]_cvars

TNext == WF_msgQ(~ABTypeInv')
TProp == \A d \in Data : (sent = d) => [](sent = d)

CSpec == ABSpec /\ TNext
=============================================================================
\* Modification History
\* Last modified Wed May 27 16:32:09 JST 2020 by daioh
\* Created Tue May 05 06:31:05 JST 2020 by daioh
