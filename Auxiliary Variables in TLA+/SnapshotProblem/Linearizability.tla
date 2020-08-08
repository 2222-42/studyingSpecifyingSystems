-------------------------- MODULE Linearizability --------------------------
\*EXTENDS Naturals
CONSTANTS Procs, Commands(_), Outputs(_), InitOutput(_), InitObj, ObjValues, Apply(_,_,_)

(*
\*Not introduces a constant ObjValues
\*but defined to complicated expression

ObjValues  == LET ApplyProcTo(i, S) == {Apply(i, cmd, x).newState : x \in S, cmd \in Commands(i)}
                  ApplyTo(S) == UNION {ApplyProcTo(i, S): i \in Procs}
                  ApplyITimes[i \in Nat] == IF i = 0 THEN {InitObj}
                                                     ELSE ApplyTo(ApplyITimes[i-1])
              IN UNION {ApplyITimes[i]: i \in Nat}
*)

ASSUME LinearAssumps ==
        /\ InitObj \in ObjValues
        /\ \A i \in Procs : InitOutput(i) \in Outputs(i)
        /\ \A i \in Procs : Outputs(i) \cap Commands(i) = {}
        /\ \A i \in Procs, obj \in ObjValues : 
            \A cmd \in Commands(i) :
                /\ Apply(i, cmd, obj).output \in Outputs(i)
                /\ Apply(i, cmd, obj).newState \in ObjValues




VARIABLES object, interface, istate
vars == <<object, interface, istate>>

Init == /\ object = InitObj
        /\ interface = [i \in Procs |-> InitOutput(i)]
        /\ istate = [i \in Procs |-> InitOutput(i)]

BeginOp(i, cmd) == /\ interface[i] \in Outputs(i)
                   /\ interface' = [interface EXCEPT ![i] = cmd] 
                   /\ istate' = [istate EXCEPT ![i] = cmd]
                   /\ object' = object

DoOp(i) == /\ interface[i] \in Commands(i)
           /\ istate[i] = interface[i]
           /\ LET result == Apply(i, interface[i], object)
              IN /\ object' = result.newState
                 /\ istate' = [istate EXCEPT ![i] = result.output]
           /\ interface' = interface 

EndOp(i) == /\ interface[i] \in Commands(i)
            /\ istate[i] \in Outputs(i)
            /\ interface' = [interface EXCEPT ![i] = istate[i]]
            /\ UNCHANGED <<object, istate>>
 

Next == \E i \in Procs : \/ \E cmd \in Commands(i) : BeginOp(i, cmd)
                         \/ DoOp(i)
                         \/ EndOp(i)

SafeSpec == Init /\ [][Next]_vars

Fairness == \A i \in Procs: WF_vars(DoOp(i)) /\ WF_vars(EndOp(i))

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================
\* Modification History
\* Last modified Sat Aug 08 16:50:24 JST 2020 by daioh
\* Created Sat Aug 08 16:06:33 JST 2020 by daioh
