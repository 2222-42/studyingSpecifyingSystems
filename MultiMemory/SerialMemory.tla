---------------------------- MODULE SerialMemory ----------------------------
EXTENDS RegisterInterface

Inner(InitMem, opQ, opOrder) == INSTANCE InnerSerial

Spec == \E InitMem \in [Adr -> Val]: \EE opQ, opOrder : Inner(InitMem, opQ, opOrder)!Spec
=============================================================================
\* Modification History
\* Last modified Sat May 02 13:50:09 JST 2020 by daioh
\* Created Wed Apr 29 11:05:52 JST 2020 by daioh
