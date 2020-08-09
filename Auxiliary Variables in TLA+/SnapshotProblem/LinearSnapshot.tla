--------------------------- MODULE LinearSnapshot ---------------------------
CONSTANTS Readers, Writers, RegVals, InitRegVal

ASSUME /\ Readers \cap Writers = {}
       /\ InitRegVal \in RegVals

Procs == Readers \cup Writers

MemVals == [Writers -> RegVals]
InitMem == [i \in Writers |-> InitRegVal]

NotMemVal == CHOOSE v: v \notin MemVals
NotRegVal == CHOOSE v: v \notin RegVals

Commands(i) = IF i \in Readers THEN {NotMemVal}
                               ELSE RegVals

Outputs(i) = IF i \in Readers THEN MemVals
                              ELSE {NotRegVal}

InitOutput(i) == IF i \in Readers THEN InitMem ELSE NotRegVal

Apply(i, cmd, obj) == IF i \in Readers
                            THEN [newState |-> obj, output |-> obj]
                            ELSE [newState |-> [obj EXCEPT ![i] = cmd], output |-> NotRegVal]

VARIABLES mem, interface, isate

INSTANCE Linearizability WITH ObjValues <- MemVals, InitObj <- InitMem, object <- mem

ASSUME LinearAssumps
=============================================================================
\* Modification History
\* Created Sun Aug 09 10:09:49 JST 2020 by daioh
