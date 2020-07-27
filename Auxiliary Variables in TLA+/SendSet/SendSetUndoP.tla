---------------------------- MODULE SendSetUndoP ----------------------------
EXTENDS SendSetUndo

Pi == {"send", "undo"}
Dom == y

PredChoose(p) == TRUE
NewPSetChoose(p) == {f \in [Dom' -> Pi] : \A d \in Dom: f[d] = p[d]}

PredSend(p) == p[x'] = "send"
NewPSetSend(p) == {[d \in Dom' |-> p[d]]}

PredRcv(p) == TRUE
NewPSetRcv(p) == {p}

PredUndo(p, S) == \A d \in S : p[d] = "undo"
NewPSetUndo(p) == {[d \in Dom' |-> p[d]]}

VARIABLES p
varsP == <<vars, p>>

InitUP == Init /\ (p = <<>>)

ChooseP == Choose /\ PredChoose(p) /\ NewPSetChoose(p)
SendP == Send /\ PredSend(p) /\ NewPSetSend(p)
RcvP == Rcv /\ PredRcv(p) /\ NewPSetRcv(p)
UndoP(S) == Undo(S) /\ PredUndo(p,S) /\ NewPSetUndo(p)

NextUP == ChooseP \/ SendP \/ RcvP \/ (\E S \in SUBSET y : UndoP(S))

SpecUP == InitUP /\ [][NextUP]_varsP


------------------------------------------------
SS == INSTANCE SendSet WITH y <- {d \in y : p[d] = "send"}
THEOREM SpecUP => SS!Spec

=============================================================================
\* Modification History
\* Created Mon Jul 27 15:46:09 JST 2020 by daioh
