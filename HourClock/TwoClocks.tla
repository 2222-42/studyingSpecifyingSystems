----------------------------- MODULE TwoClocks -----------------------------
EXTENDS Naturals

VARIABLES x, y
CONSTANT Clock

HCN(h) == h' = (h % 12) + 1

hr == [k \in Clock |-> 1..12]

hrfcn == [k \in Clock |-> hr[k]]

IsFcnOn(f, S) == f = [z \in S |-> f[z]]

HCS == (hr \in 1..12) /\ [][HCN(hr)]_hr

TwoClocks == /\ (x \in 1..12) /\ [][HCN(x)]_x
             /\ (y \in 1..12) /\ [][HCN(y)]_y

TCNext == \/ HCN(x) /\ HCN(y)
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

ClockArray == \A k \in Clock: (hr[k] \in 1..12) /\ [][HCN(hr[k])]_(hr[k])
LClockArray == \A k \in Clock: (hr[k] \in 1..12) /\ [][HCN(hr[k])]_(hr[k]) /\ WF_{hr[k]}(HCN(hr[k]))

ACN(k) == /\ hr'[k] = (hr[k] % 12) + 1
          /\ \A i \in Clock\{k}: hr'[i] = hr[i]
EANC(k) == [hr EXCEPT ![k] = (hr[k] % 12) + 1]
HEANC(k) == hrfcn' = [hrfcn EXCEPT ![k] = (hr[k] % 12) + 1]

EClockarray == \A k \in Clock: (hr[k] \in 1..12) /\ [][EANC(k)]_k

Spec == /\ []IsFcnOn(hr, Clock)
        /\ EClockarray

=============================================================================
\* Modification History
\* Last modified Sun Apr 12 20:54:37 JST 2020 by daioh
\* Created Fri Apr 03 00:35:39 JST 2020 by daioh
