--------------------------- MODULE AfekSimplified ---------------------------
EXTENDS  Integers
CONSTANTS Readers, Writers, RegVals, InitRegVal

MemVals == [Writers -> RegVals]
InitMem == [i \in Writers |-> InitRegVal]
NotMemVal == CHOOSE v: v \notin MemVals
NotRegVal == CHOOSE v: v \notin RegVals

IRegVals == RegVals \X Nat
IMemVals == [Writers -> IRegVals]
InitIMem == [i \in Writers |-> <<InitRegVal, 0>>]

VARIABLES interface, imem, wrNum, rdVal1, rdVal2
vars == <<interface, imem, wrNum, rdVal1, rdVal2>>

Init == /\ imem = InitIMem
        /\ interface = [i \in Readers \cup Writers |->
                        IF i \in Readers THEN InitMem ELSE  NotRegVal ]
        /\ wrNum = [i \in Writers |-> 0]
        /\ rdVal1 = [i \in Readers |-> <<>>]
        /\ rdVal2 = [i \in Readers |-> <<>>]

BeginWr(i, cmd) == /\ interface[i] = NotRegVal
                   /\ wrNum' = [wrNum EXCEPT ![i] = wrNum[i] + 1]
                   /\ interface' = [interface EXCEPT ![i] = cmd]
                   /\ UNCHANGED <<imem, rdVal1, rdVal2>>

(* 
because 
1. wrNum[i] counts the number of BeginWr(i, cmd) steps and
2. imem[i][2] is set to wrNum[i] by the DoWr(i)
,
when imem[i][2] equals wrNum[i]
- EndWrite(i) action should be enabled and 
- DoWr(i) disabled 
. *)
DoWr(i) == /\ interface[i] \in RegVals
           /\ imem[i][2] # wrNum[i]
           /\ imem' = [imem EXCEPT ![i] = <<interface[i], wrNum[i]>>]
           /\ UNCHANGED <<interface, wrNum, rdVal1, rdVal2>>

EndWr(i) == /\ interface[i] \in RegVals
            /\ imem[i][2] = wrNum[i]
            /\ interface' = [interface EXCEPT ![i] = NotRegVal]
            /\ UNCHANGED <<imem, wrNum, rdVal1, rdVal2>>

BeginRd(i) == /\ interface[i] \in MemVals
              /\ interface' = [interface EXCEPT ![i] = NotMemVal]
              /\ UNCHANGED <<imem, wrNum, rdVal1, rdVal2>>

AddToFcn(f, x, v) == [y \in (DOMAIN  f) \cup {x} |-> IF y = x THEN v ELSE  f [y]]


Rd1(i) == /\ interface[i] \in NotMemVal
          /\ \E j \in Writers \ DOMAIN rdVal1[i]:
                rdVal1' = [rdVal1 EXCEPT ![i] = AddToFcn(rdVal1[i], j, imem[j])]
          /\ UNCHANGED <<interface, imem, wrNum, rdVal2>>

Rd2(i) == /\ interface[i] \in NotMemVal
          /\ DOMAIN rdVal1[i] = Writers
          /\ \E j \in Writers \ DOMAIN rdVal2[i]:
                rdVal2' = [rdVal2 EXCEPT ![i] = AddToFcn(rdVal2[i], j, imem[j])]
          /\ UNCHANGED <<interface, imem, wrNum, rdVal1>>

TryEndRd(i) == /\ interface[i] \in NotMemVal
               /\ DOMAIN rdVal1[i] = Writers
               /\ DOMAIN rdVal2[i] = Writers
               /\ IF rdVal1[i] = rdVal2[i]
                    THEN interface' = [interface EXCEPT ![i] = [j \in Writers |-> rdVal1[i][j][1]]]
                    ELSE interface' = interface
               /\ rdVal1' = [rdVal1 EXCEPT ![i] = <<>>]
               /\ rdVal2' = [rdVal2 EXCEPT ![i] = <<>>]
               /\ UNCHANGED <<imem, wrNum>>

Next == \/ \E i \in Readers: BeginRd(i) \/ Rd1(1) \/ Rd2(i) \/ TryEndRd(i)
        \/ \E i \in Writers: \/ \E cmd \in RegVals : BeginWr(i, cmd)
                             \/ DoWr(i) \/ EndWr(i)

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Created Sun Aug 09 10:46:27 JST 2020 by daioh
