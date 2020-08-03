---------------------------- MODULE SendSeqUndoP ----------------------------
EXTENDS SendSeqUndo

Pi == {"send", "undo"}
Dom == DOMAIN y

INSTANCE Prophecy WITH DomPrime <- Dom'

PredDomChoose == {}
DomInjChoose == [d \in Dom |-> d]
PredChoose(p) == TRUE

PredDomSend == {1}
DomInjSend == [i \in 2..Len(y) |-> i - 1]
PredSend(p) == p[1] = "srend"

PredDomRcv == {}
DomInjRcv == [d \in Dom |-> d]
PredRcv(p) == TRUE

PredDomUndo(i) == {i}
DomInjUndo(i) == [j \in 1..Len(y)\{i} |-> IF j < i THEN j ELSE j - 1]
PredUndo(p, i) == p[i] = "undo"

Condition ==
    /\ ProphCondition(Choose, DomInjChoose, PredDomChoose, PredChoose)
    /\ ProphCondition(Send, DomInjSend, PredDomSend, PredSend)
    /\ ProphCondition(Rcv, DomInjRcv, PredDomRcv, PredRcv)
    /\ \E i \in Dom :
        ProphCondition(Undo(i), DomInjUndo(i), PredDomUndo(i ),
                        LAMBDA  p : PredUndo(p, i))

THEOREM  SpecU => [][Condition]_vars

---------------------------------------------------------------

VARIABLE p
varsP == <<vars, p>>

InitUP == Init /\ (p \in [Dom -> Pi])

ChooseP == ProphAction(Choose, p, p',  DomInjChoose, DomInjChoose, PredChoose)
SendP == ProphAction(Send, p, p', DomInjSend, DomInjSend, PredSend)
RcvP == ProphAction(Rcv, p, p', DomInjRcv, DomInjRcv, PredRcv)
UndoP(i) == ProphAction(Undo(i), p, p', DomInjUndo(i), DomInjUndo(i), LAMBDA j: PredUndo(j, i))

NextUP == ChooseP \/ SendP \/ RcvP \/ (\E i \in 1..Len(y): UndoP(i))

SpecUP == InitUP /\ [][NextUP]_varsP

yBar == 
    LET RECURSIVE R(_, _)
        R(yseq, pseq) ==
            IF yseq = <<>>
                THEN yseq
                ELSE IF Head(pseq) = "send"
                        THEN <<Head(yseq)>> \o R(Tail(yseq), Tail(pseq))
                        ELSE R(Tail(yseq), Tail(pseq))
    IN R(y,p)

SS == INSTANCE SendSeq WITH y <- yBar

THEOREM SpecUP => SS!Spec

=============================================================================
\* Modification History
\* Last modified Mon Aug 03 10:28:09 JST 2020 by daioh
\* Created Wed Jul 29 10:23:05 JST 2020 by daioh
