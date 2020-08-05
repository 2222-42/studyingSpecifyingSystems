------------------------------ MODULE HourMin ------------------------------
EXTENDS Integers

VARIABLE h, m

Init == /\ (h = 0) /\ (m = 0)

Next == /\ m' = (m+1)%60
        /\ h' = IF m' = 0 THEN (h+1)%24 ELSE h

Spec == Init /\ [][Next]_h

=============================================================================
\* Modification History
\* Created Wed Aug 05 16:23:26 JST 2020 by daioh
