------------------------- MODULE RealTimeHourClock -------------------------
EXTENDS Reals, HourClock

VARIABLE now
CONSTANT Rho
ASSUME (Rho \in Real) /\ (Rho > 0)
------------------------------------------------------------

  ----------------------- MODULE Inner -----------------------
    VARIABLE t
    TNext == t' = IF HCnxt THEN 0 ELSE t + (now' - now)
    Timer == (t = 0) /\ [][TNext]_<<t, hr, now>>
    MaxTime == [](t <= 3600 + Rho)
    MinTime == [][HCnxt => (t >= 3600 - Rho)]_hr
    HCTime == Timer /\ MaxTime /\ MinTime
  ==============================================

I(t) == INSTANCE Inner

NowNext == /\ now' \in {r \in Real: r > now}
           /\ UNCHANGED hr

RTnow == /\ now \in Real 
         /\ [][NowNext]_now
         /\ \A r \in Real: WF_now(NowNext /\ now' > r)

RTHC == HC /\ RTnow /\ (\EE t: I(t)!HCTime)
=============================================================================
\* Modification History
\* Last modified Sat Mar 14 20:19:56 JST 2020 by daioh
\* Created Thu Mar 12 10:35:25 JST 2020 by daioh
