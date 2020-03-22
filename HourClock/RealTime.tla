------------------------------ MODULE RealTime ------------------------------

EXTENDS Reals
VARIABLES now
--------------------------------------------
RTBound(A, v, D, E) 
    == LET  TNext(t) == t' = IF <<A>>_v \/ \neg (ENABLED <<A>>_v)'
                            THEN 0
                            ELSE t + (now' - now)
            Timer(t) == (t = 0) /\ [][TNext(t)]_<<t, v, now>>
            MaxTime(t) == [](t <= E)
            MinTime(t) == [][A => (t >= D)]_v
        IN \EE t: Timer(t) /\ MaxTime(t) /\ MinTime(t)

--------------------------------------------
RTnow(v) == 
    LET NowNext == /\ now' \in {r \in Real : r > now}
                    /\ UNCHANGED v
    IN  /\ now \in Real 
        /\ [][NowNext]_now
        /\ \A r \in Real: WF_now(NowNext /\ now' > r)

    (* 
        /\ now' \in {r \in Real: r> now}
        /\ <<p', w'>>  = Integrate(D, now, now', <<p,w>>)
        /\ UNCHANGED v
     *)

=============================================================================
\* Modification History
\* Last modified Sat Mar 14 23:25:37 JST 2020 by daioh
\* Created Sat Mar 14 22:52:54 JST 2020 by daioh
