----------------------------- MODULE SendInt1P -----------------------------
EXTENDS SendInt1

Pi == Int

PredSend(i) == x' = i

VARIABLE p

varsP == <<x, p>>

InitP == Init /\ (p \in Pi)

SendP == Send /\ PredSend(p) /\ (p' \in Pi)

RcvP == Rcv /\ (p' = p)

NextP == SendP \/ RcvP

SpecP == InitP /\ [][NextP]_varsP

---------------------------------------------------------------------------

SI2 == INSTANCE SendInt2 WITH z <- IF x = NotInt THEN p ELSE NotInt

THEOREM SpecP => SI2!Spec
=============================================================================
\* Modification History
\* Created Fri Jul 17 14:54:06 JST 2020 by daioh
