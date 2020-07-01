------------------------------ MODULE MinMax1 ------------------------------
(* The purpose of this specication is to describe the interaction of the user
and the server. *)

EXTENDS Integers

\* What the server respond to user
CONSTANTS Hi, Lo, Both, None
\* The values of responses and of inputs should be separeted.
ASSUME {Hi, Lo, Both, None} \cap Int = {}

\* This interaction is described by the values of x and turn. (externally visible or observable)
\* y is needed only to describe how the values of x and turn can change.(Internal variable)
VARIABLES x, y, turn

Init == /\ x = None
        /\ turn = "input"
        /\ y = {}

\* user's input action
InputNum == /\ turn = "input"
            /\ turn' = "output"
            /\ x' \in Int
            /\ y' = y


setMax(S) == CHOOSE t \in S: \A s \in S : t >= s
setMin(S) == CHOOSE t \in S: \A s \in S : t <= s

(* To define the action Respond, it is needed to make above functions setMax and setMin. *)
\* the server's output action
Respond == /\ turn = "output"
           /\ turn' = "input"
           /\ y' = y \cup {x}
           /\ x' = IF x = setMax(y')
                    THEN IF x = setMin(y') THEN Both ELSE Hi
                    ELSE IF x = setMin(y') THEN Lo ELSE None

Next == InputNum \/ Respond

vars == <<x, turn, y>>

Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Created Mon Jun 29 12:35:58 JST 2020 by daioh
