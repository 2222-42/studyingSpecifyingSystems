-------------------------------- MODULE Hour --------------------------------
EXTENDS Integers

VARIABLE h

Init == h = 0

Next == h' = (h + 1) % 24

Spec == Init /\ [][Next]_h

\* Spec1 == (h = 0) /\ [][h' = (h + 1) % 24]_h
\* Spec2 == /\ (h = 0) /\ (m = 0)
\*          /\ [][/\ m' = (m+1)%60
\*                /\ h' = IF m' = 0 THEN (h+1)%24 ELSE h]_<<h, m>>

=============================================================================
\* Modification History
\* Created Mon Aug 03 10:30:47 JST 2020 by daioh
