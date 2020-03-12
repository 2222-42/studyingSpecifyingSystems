----------------------------- MODULE HourClock -----------------------------
    (**********************************************)
    (* This moduel sssss ssssssssssssssssssssssss *)
    (**********************************************)

EXTENDS Naturals

VARIABLE hr \* variable hr represents the dsplay

HCini == hr \in (1 .. 12) \* Initially, hr can have any value from 1 through 12.

HCnxt (* This is a wired place for a comment. *) ==
    (**********************************************)
    (* The value of hr cycles from 1 through 12 *)
    (**********************************************)
    hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr
(* The complete spec. It permits the clock to stop. *)

------------------------------------------------

THEOREM HC => []HCini \* Type-correctness of the spec.

=============================================================================
\* Modification History
\* Created Sat Jan 25 23:42:09 JST 2020 by daioh
