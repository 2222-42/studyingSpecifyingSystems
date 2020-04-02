----------------------------- MODULE TwoClocks -----------------------------
EXTENDS Naturals

VARIABLE hr

HCN(h) == h' = (hr % 12) + 1

HCS == (hr \in 1..12) /\ [][HCN(hr)]_hr

TwoClocks == /\ (x \in 1..12) /\ [][HCN(x)]_x
             /\ (y \in 1..12) /\ [][HCN(y)]_y

TCNext == \/ HNC(x) /\ HCN(y)
          \/ HCN(x) /\ (y' = y)
          \/ HCN(y) /\ (x' = x)

HCNx == HCN(x) /\ (y' = y)
HCNy == HCN(y) /\ (x' = x)

(* the way to disallow simultaneous change to both clock display
TwoClocks /\ [][(x' = x) \/ (y' = y)]_<<x, y>>
*)

NTwoClocks == /\ (x \in 1..12) /\ (y \in 1..12)
              /\ [][\/ HCNx /\ (y' = y) 
                    \/ HCNy /\ (x' = x)]_<<x, y>>



=============================================================================
\* Modification History
\* Created Fri Apr 03 00:35:39 JST 2020 by daioh
