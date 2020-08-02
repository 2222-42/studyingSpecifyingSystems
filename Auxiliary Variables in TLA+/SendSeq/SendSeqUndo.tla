---------------------------- MODULE SendSeqUndo ----------------------------
EXTENDS SendSeq

RemoveEltFrom(i, seq) == [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j+1]]

Undo(i) == /\ y' = RemoveEltFrom(i, y)
           /\ x' = x

NextU == Next \/ (\E i \in 1..Len(y): Undo(i))

SpecU == Init /\ [][NextU]_vars

Condition ==
    /\ ProphCondition(Choose, DomInjChoose, PredDomChoose, PredChoose)
    /\ ProphCondition(Send, DomInjSend, PredDomSend, PredSend)
    /\ ProphCondition(Rcv, DomInjRcv, PredDomRcv, PredRcv)
    /\ \E i \in Dom :
        ProphCondition(Undo(i), DomInjUndo(i), PredDomUndo(i ),
                        LAMBDA  p : PredUndo(p, i))

THEOREM  SpecU => [][Condition]_vars

=============================================================================
\* Modification History
\* Created Wed Jul 29 10:04:26 JST 2020 by daioh
