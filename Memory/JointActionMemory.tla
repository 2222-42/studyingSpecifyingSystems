------------------------- MODULE JointActionMemory -------------------------
EXTENDS MemoryInterface
--------------------- MODULE InnerEnvironmentComponent ---------------------
(*E for Environment.*)
VARIABLES rdy
IE == rdy = [p \in Proc |-> TRUE]

ERqst(p) ==
    /\ rdy[p]
    /\ \E req \in MReq : Send(p, req, memInt, memInt')
    /\ rdy' = [rdy EXCEPT ![p] = FALSE]

ERsp(p) == 
    /\ \E rsp \in Val \cup {NoVal}: Reply(p, rsp, memInt, memInt')
    /\ rdy' = [rdy EXCEPT ![p] = TRUE]

NE == \E p \in Proc: ERqst(p) \/ ERsp(p)
IESpec == IE /\ [][NE]_<<memInt, rdy>>
=============================================================================

------------------------- MODULE InnerMemoryComponent -----------------------
(*M for memory Component.*)
\* MRsp(p) be the same as the action Rsp(p)
\* MInternal be the same as the action Do(p)
EXTENDS InternalMemory

\* IM == IInit

MRqst(p) ==
    /\ \E req \in MReq:
        /\ Send(p, req, memInt, memInt')
        /\ buf' = [buf EXCEPT ![p] = req]
        /\ ctl' = [ctl EXCEPT ![p] = "busy"]
    /\ UNCHANGED mem

NM == \E p \in Proc: MRqst(p) \/ Rsp(p) \/ Do(p)
IMSpec == IInit /\ [][NM]_<<memInt, buf, ctl, mem>>
=============================================================================
IEnv(rdy) == INSTANCE InnerEnvironmentComponent
IMem(mem, ctl, buf) == INSTANCE InnerMemoryComponent

Spec == /\ \EE rdy: IEnv(rdy)!IESpec
        /\ \EE mem, ctl, buf: IMem(mem, ctl, buf)!IMSpec
=============================================================================
\* Modification History
\* Created Wed Apr 08 23:46:16 JST 2020 by daioh
