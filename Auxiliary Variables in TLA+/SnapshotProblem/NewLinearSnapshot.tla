------------------------- MODULE NewLinearSnapshot -------------------------
EXTENDS Integers, Sequences

CONSTANTS Readers, Writers, RegVals, InitRegVal

ASSUME /\ Readers \cap Writers = {}
       /\ InitRegVal \in RegVals

MemVals == [Writers -> RegVals]
InitMem == [i \in Writers |-> InitRegVal]

NotMemVal == CHOOSE v: v \notin MemVals
NotRegVal == CHOOSE v: v \notin RegVals

VARIABLES mem, interface, wstate, rstate
vars == <<mem, interface, wstate, rstate>>

Init == /\ mem = InitMem
        /\ interface = [i \in Readers \cup Writers |->
                        IF i \in Readers THEN InitMem ELSE  NotRegVal ]
        /\ wstate = [i \in Writers |-> NotRegVal]
        /\ rstate = [i \in Readers |-> <<>>]

BeginWr(i, cmd) == /\ interface[i] = NotRegVal
                   /\ interface' = [interface EXCEPT ![i] = cmd]
                   /\ wstate' = [wstate EXCEPT ![i] = cmd]
                   /\ UNCHANGED <<mem, rstate>>

BeginRd(i) == /\ interface[i] \in MemVals
              /\ interface' = [interface EXCEPT ![i] = NotMemVal]
              /\ rstate' = [rstate EXCEPT ![i] = <<mem>>]
              /\ UNCHANGED <<mem, wstate>>

DoWr(i) == /\ interface[i] \in RegVals
           /\ wstate[i] = interface[i]
           /\ mem' = [mem EXCEPT ![i] = interface[i]]
           /\ wstate' = [wstate EXCEPT ![i] = NotRegVal]
           /\ rstate' = [j \in Readers |-> IF rstate[j] = <<>> THEN <<>> ELSE Append(rstate[j], mem')]
           /\ interface' = interface

EndRd(i) == /\ interface[i] = NotMemVal
            /\ \E j \in 1..Len(rstate[i]):
                interface' = [interface EXCEPT ![i] = rstate[i][j]]
            /\ rstate' = [rstate EXCEPT ![i] = <<>>]
            /\ UNCHANGED <<mem, wstate>>

EndWr(i) == /\ interface[i] \in RegVals
            /\ wstate[i] = NotRegVal
            /\ interface' = [interface EXCEPT ![i] = wstate[i]]
            /\ UNCHANGED <<mem, rstate, wstate>>

Next == \/ \E i \in Readers: BeginRd(i) \/ EndRd(i)
        \/ \E i \in Writers: \/ \E cmd \in RegVals : BeginWr(i, cmd)
                             \/ DoWr(i) \/ EndWr(i)

SafeSpec == Init /\ [][Next]_vars

Fairness == /\ \A i \in Readers : WF_vars(EndRd(i))
            /\ \A i \in Writers : WF_vars(DoWr(i)) /\ WF_vars(EndWr(i))

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================
\* Modification History
\* Created Mon Aug 10 16:23:00 JST 2020 by daioh
