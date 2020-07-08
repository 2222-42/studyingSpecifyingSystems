------------------------------ MODULE MinMax2H ------------------------------
\* The initial predicate and next-state action of Spec^h_2
\* are the same as those of Spec2,
\* So Extends MinMax2
EXTENDS MinMax2

\* h is history variable
VARIABLE h

InitH == Init /\ (h = {})

InputNumH == /\ InputNum
             /\ h' = h

RespondH == /\ Respond
            /\ h' = h \cup {x}

\* Next == InputNum \/ Respond
NextH == InputNumH \/ RespondH

varsH == <<vars, h>>

\* Spec == Init /\ [][Next]_vars
SpecH == InitH /\ [][NextH]_varsH

M == INSTANCE MinMax1
        WITH y <- h

THEOREM SpecH => M!Spec
=============================================================================
\* Modification History
\* Created Wed Jul 08 14:00:54 JST 2020 by daioh
