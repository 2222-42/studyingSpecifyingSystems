------------------------- MODULE RegisterInterface -------------------------
CONSTANT Adr,
         Val,
         Proc,
         Reg

VARIABLE regFile \* `regFile[p][r]` represents the contents of register `r` of processor `p`.

---------------------------------------------------------------------------

RdRequest == [adr: Adr, val: Val, op: {"Rd"}]
WrRequest == [adr: Adr, val: Val, op: {"Wr"}]
FreeRegValue == [adr: Adr, val: Val, op: {"Free"}]
Request == RdRequest \cup WrRequest
RegValue == Request \cup FreeRegValue
RegFileTypeInvariant ==
    regFile \in [Proc -> [Reg -> RegValue]]
=============================================================================
\* Modification History
\* Created Mon Apr 27 16:30:22 JST 2020 by daioh
