-------------------------------- MODULE FIFO --------------------------------
CONSTANT Message
VARIABLES in, out

Inner(q) == INSTANCE InnerFIFO

Spec == \E q: Inner(q)!Spec


=============================================================================
\* Modification History
\* Last modified Sat Feb 01 18:20:08 JST 2020 by daioh
\* Created Sat Feb 01 18:19:48 JST 2020 by daioh
