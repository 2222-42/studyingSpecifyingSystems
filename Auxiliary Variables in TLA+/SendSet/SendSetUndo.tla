---------------------------- MODULE SendSetUndo ----------------------------
EXTENDS SendSet

Undo(S) == /\ y' = y \ S
           /\ x' = x

NextU == Next \/ (\E S \in (SUBSET y): Undo(S))

SpecU == Init /\ [][NextU]_vars

=============================================================================
\* Modification History
\* Created Sun Jul 26 17:21:35 JST 2020 by daioh
