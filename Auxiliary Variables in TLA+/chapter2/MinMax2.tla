------------------------------ MODULE MinMax2 ------------------------------

EXTENDS Integers

CONSTANTS None, Hi, Lo, Both

VARIABLES x, turn, min, max

\* To declare these two in the statement CONSTANTS let us to add an ASSUME statement.
\* So define just like the following.
Infinity == CHOOSE n : n \notin Int
MinusInfinity == CHOOSE n : n \notin (Int \cup {Infinity})

\* In integers, (Minus/)Infinity <= x is not defined, so we have to define new two relations
IsLeq(i, j) == (j = Infinity) \/ (i <= j)
IsGeq(i, j) == (j = MinusInfinity) \/ (i >= j)

Init == /\ x = None
        /\ turn = "input"
        /\ min = Infinity
        /\ max = MinusInfinity

InputNum == /\ turn = "input"
            /\ turn' = "output"
            /\ x' \in Int
            /\ UNCHANGED <<min, max>> \* This is same as y' = y

Respond == /\ turn = "output"
           /\ turn' = "input"
           \*    /\ y' = y \cup {x}
           /\ min' = IF IsLeq(x, min) THEN x ELSE min
           /\ max' = IF IsGeq(x, max) THEN x ELSE max
           /\ x' = IF x = max'
                    THEN IF x = min' THEN Both ELSE Hi
                    ELSE IF x = min' THEN Lo ELSE None

Next == InputNum \/ Respond

vars == <<x, turn, min, max>>

Spec == Init /\ [][Next]_vars

LSpec == Init /\ [][Next]_vars /\ WF_vars (Respond)

=============================================================================
\* Modification History
\* Created Sat Jul 04 13:20:22 JST 2020 by daioh
