------------------------------- MODULE Memory -------------------------------
EXTENDS MemoryInterface

Inner(mem, ctl, buf) == INSTANCE InternalMemory

Spec == \EE mem, ctl, buf: Inner(mem, ctl, buf)!ISpec

=============================================================================
\* Modification History
\* Last modified Mon Feb 03 09:36:08 JST 2020 by daioh
\* Created Mon Feb 03 09:35:06 JST 2020 by daioh
