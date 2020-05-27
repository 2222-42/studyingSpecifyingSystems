----------------------------- MODULE HourClock -----------------------------
    (**********************************************)
    (* This moduel sssss ssssssssssssssssssssssss *)
    (**********************************************)

EXTENDS Naturals

VARIABLE hr \* variable hr represents the dsplay

HCini == hr \in (1 .. 12) \* Initially, hr can have any value from 1 through 12.

(*

In essence the problem is that writing something like

(1)  \A x \in S : f[x] = e

is weaker than writing

(2)  f = [x \in S |-> e]

because (1) doesn't tell us that the domain of f is S, or in fact that f is a function. You can strengthen (2) by writing

(3) f \in [S -> T] /\ \A x \in S : f[x] = e

for some suitable set T
*)
(*
AnyClocks1 ==
  /\ [](hr \in [Clock -> 1 .. 12])
  /\ \A c \in Clock : C!Spec(hr[c])

AnyClocks2 == 
  /\ \A c \in Clock : (hr \in [Clock -> 1 .. 12]) /\ C!Init(hr[c])
  /\ [][ /\ hr' \in [Clock -> 1 .. 12]
         /\ \A c \in Clock : [C!Next(hr[c])]_<<hr[c]>>
       ]_<<hr>>
*)

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
