---------------------------- MODULE SendSeqUndo ----------------------------
EXTENDS SendSeq

RemoveEltFrom(i, seq) == [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j+1]]

Undo(i) == /\ y' = RemoveEltFrom(i, y)
           /\ x' = x

NextU == Next \/ (\E i \in 1..Len(y): Undo(i))

SpecU == Init /\ [][NextU]_vars

=============================================================================
\* Modification History
\* Last modified Mon Aug 03 10:27:57 JST 2020 by daioh
\* Created Wed Jul 29 10:04:26 JST 2020 by daioh
