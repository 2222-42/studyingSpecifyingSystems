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

---------------------------------------------------
vars == h
VARIABLES s
INSTANCE Stuttering

InitS == Init /\ (s = top)

\* Next is always enabled, so enabled Next equals true.
(* Since we are adding stuttering steps to only one action, it doesn't matter 
 what constant we choose for the actionId argument*)
(*Next, which is the only subaction in the trivial disjunctive representation
of Next, has a null context.*)
NextS == PreStutter(Next, TRUE, "Next", "", 59, 1, LAMBDA j: j + 1)

SpecS == InitS /\ [][NextS]_<<vars, s>>

HM == INSTANCE HourMin WITH m <- IF s = top THEN 0 ELSE s.val

THEOREM SpecS => HM!Spec

=============================================================================
\* Modification History
\* Created Mon Aug 03 10:30:47 JST 2020 by daioh
