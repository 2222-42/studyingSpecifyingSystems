--------------------------- MODULE CompositeFIFO ---------------------------
EXTENDS Naturals, Sequences

CONSTANT Message
VARIABLES in, out

-----------------------------------------------------------------------------

InChan == INSTANCE Channel WITH Data <- Message, chan <- in
OutChan == INSTANCE Channel WITH Data <- Message, chan <- out

-----------------------------------------------------------------------------

(*
Init == 
    /\ InChan!Init
    /\ OutChan!Init
    /\ q = <<>>

TypeInvariant ==
    /\ InChan!TypeInvariant
    /\ OutChan!TypeInvariant
    /\ q \in Seq(Message)

*)

(*
InnerFIFO:
SSend(msg) == 
    /\ InChan!Send(msg)
    /\ UNCHANGED <<out, q>>

*)


SenderInit == (in.rdy \in {0, 1}) /\ (in.val \in Message)
Sender == SenderInit /\ [][\E msg \in Message: InChan!Send(msg)]_<<in.val, in.rdy>>

-----------------------------------------------------------------------------
------------------------------ MODULE InnerBuf ------------------------------
VARIABLE q

BufferInit == /\ in.ack \in {0.1}
              /\ q = <<>>
              /\ (out.rdy \in {0,1}) /\ (out.val \in Message)

BufRcv ==
    /\ InChan!Rcv
    /\ q' = Append(q, in.val)
    /\ UNCHANGED <<out.val, out.rdy>>
(*  /\ UNCHANGED out *)

BufSend ==
    /\ q # <<>>
    /\ OutChan!Send(Head(q))
    /\ q' = Tail(q)
    /\ UNCHANGED in.ack
(*  /\ UNCHANGED in *)

InnerBuffer == BufferInit /\ [][BufRcv \/ BufSend]_<<in.ack, q, out.val, out.rdy>>
=============================================================================

Buf(q) == INSTANCE InnerBuf
Buffer == \EE q: Buf(q)!InnerBuffer
-----------------------------------------------------------------------------
(*
InncerFIFO
RRcv ==
    /\ OutChan!Rcv
    /\ UNCHANGED <<in, q>>
Channel: 
Rcv ==
    /\ chan.rdy /= chan.ack
    /\ chan' = [chan EXCEPT !.ack = 1 - @]    
*)
ReceiverInit == out.ack \in {0, 1}
Receiver == ReceiverInit /\ [][OutChan!Rcv]_{out.ack}
(* `[][OutChan!Rcv]_out.ack` cause Parse Error: "[] follwoed by action not of form `[A]_v`*)
(* So I use `_(out.ack)` or `_{out.ack}` as `_v`. *)
(* I should check the syntax of tlaplus. *)

-----------------------------------------------------------------------------
(*
Next ==
    \/ \E msg \in Message: SSend(msg)
    \/ BufRcv
    \/ BufSend
    \/ RRcv
*)

(*Spec == Init /\ [][Next]_<<in, out, q>>*)

IsChannel(c) == c = [ack |-> c.ack, val |-> c.val, rdy |-> c.rdy]

Spec == /\ [](IsChannel(in) /\ IsChannel(out)) 
        /\ (in.ack = in.rdy) /\ (out.ack = out.rdy)
        /\ Sender /\ Buffer /\ Receiver

OpenSpec == /\ [](IsChannel(in) /\ IsChannel(out)) 
            /\ (in.ack = in.rdy) /\ Sender /\ Receiver 
              -+-> (out.ack = out.rdy) /\ Buffer
=============================================================================
\* Modification History
\* Last modified Sun Apr 05 00:28:54 JST 2020 by daioh
\* Created Sat Apr 04 23:45:51 JST 2020 by daioh
