---------------------------- MODULE TrainSiding ----------------------------

\*The first step in modeling is always to decide what to include in the model and what to exclude. 

\*The first thing I needed to decide was which variables describe the model. 
\* two variables for the position of the trains (t1 and t2)
\*Four variables for the signal of each semaphore (s1 to s4)
\*two variables for the position of the switches (sw1 and sw2).
VARIABLES t1, t2, s1, s2, s3, s4, sw1, sw2

Init == /\ t1 = "TRACK1"
        /\ t2 = "TRACK2"
        /\ s1 = "STOP"
        /\ s2 = "STOP"
        /\ s3 = "STOP"
        /\ s4 = "STOP"
        /\ sw1 = "STRAIGHT"
        /\ sw2 = "STRAIGHT"

Positions == {"TRACK1", "TRACK2", "TRACK3", "TRACK4", "SWITCH1", "SWITCH2"}

Signals == {"STOP", "GO"}

TypeInvariants == /\ t1 \in Positions
                  /\ t2 \in Positions
                  /\ s1 \in Signals
                  /\ s2 \in Signals
                  /\ s3 \in Signals
                  /\ s4 \in Signals
                  /\ sw1 \in {"STRAIGHT", "LEFT"}
                  /\ sw2 \in {"STRAIGHT", "RIGHT"}

\* GOALs or Terminations, and Liveness
NoCollisions == t1 # t2

Train1Crossed == t1 = "TRACK4"
Train2Crossed == t2 = "TRACK1"
CrossingSuccessful == <>Train1Crossed /\ <>Train2Crossed

(*
John Gall "A complex system that works is invariably found to have evolved from a simple system that worked."
-> begin with the simplest behavior possible
*)

\* Move Train 1 in a straight line
MoveT1 == /\ /\ \/ t1 = "TRACK1"
                \/ t1' = "SWITCH1"
             /\ \/ t1 = "SWITCH1"
                \/ t1' = "TRACK2"
             /\ \/ t1 = "TRACK2"
                \/ t1' = "SWITCH2"
             /\ \/ t1 = "SWITCH2"
                \/ t1' = "TRACK4"
          /\ UNCHANGED <<t2, s1, s2, s3, s4, sw1, sw2>>

\* Move Train 2 in a straight line
MoveT2 == /\ /\ \/ t2 = "TRACK4"
                \/ t2' = "SWITCH2"
             /\ \/ t2 = "SWITCH2"
                \/ t2' = "TRACK2"
             /\ \/ t2 = "TRACK2"
                \/ t2' = "SWITCH1"
             /\ \/ t2 = "SWITCH1"
                \/ t2' = "TRACK1"
          /\ UNCHANGED <<t1, s1, s2, s3, s4, sw1, sw2>>

\* First Specification

 Next == MoveT1 \/ MoveT2
 Spec == Init /\ [][Next]_vars 


=============================================================================
\* Modification History
\* Last modified Fri Jun 26 17:35:51 JST 2020 by daioh
\* Created Fri Jun 26 17:29:19 JST 2020 by daioh
