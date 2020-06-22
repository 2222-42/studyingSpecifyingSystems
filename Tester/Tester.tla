------------------------------- MODULE Tester -------------------------------
(* a "tester" module that imports another "spec" module *)
(* cf: [tlaplus] Using TLA VARIABLES in PlusCal algorithm *)

EXTENDS \*Whatever
CONSTANTS \*Things
(*
the pcal translator runs in a separate context entirely from the rest of the specification.
The `variables` statement inside of the algorithm will introduce a VARIABLES declaration in the translation

where it does not recognize INSTANCE Core WITH VarA <- A, VarB <- B as valid. I think it's the comma being a problem.

VARIABLES A, B
INSTANCE Core WITH VarA <- A, VarB <- B
*)

(*--algorithm maketest

variables
  A = {}, B = {}; \* A and B implicitly substitute same-named variables from Core module.
                  \* due to what might be a bug in the PlusCal translator

define
  TestCore == INSTANCE Core   \* Instantiate Core within PlusCal context.
end define;

\* A and B can now be used in rest of PlusCal algorithm.
\* Other operators from Core can be used with TestCore!OperatorName .

end algorithm; *)


=============================================================================
\* Modification History
\* Last modified Mon Jun 22 17:20:41 JST 2020 by daioh
\* Created Mon Jun 22 17:15:37 JST 2020 by daioh
