----------------------------- MODULE BoudedFIFO -----------------------------
EXTENDS Naturals, Sequences

CONSTANT Message, N

VARIABLES in, out

ASSUME (N \in Nat) /\ (N > 0)

Inner(q) == INSTANCE InnerFIFO

BNext(q) == 
    /\ Inner(q)!Next
    /\ Inner(q)!BufRcv => (Len(q) < N)

Spec == \E q: Inner(q)!Init /\ [][BNext(q)]_<<in, out, q>>

=============================================================================
\* Modification History
\* Created Sat Feb 01 18:39:06 JST 2020 by daioh
