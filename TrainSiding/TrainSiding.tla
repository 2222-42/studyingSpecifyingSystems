---------------------------- MODULE TrainSiding ----------------------------

\* This module is derived from stefan's good example.(cf: https://www.heinbockel.eu/2019/12/08/train-sidings-a-tla-example/ )
\* I read his posts, make his spec by myself and improve this to solve his question.

\*The first step in modeling is always to decide what to include in the model and what to exclude. 

\*The first thing I needed to decide was which variables describe the model. 
\* two variables for the position of the trains (t1 and t2)
\*Four variables for the signal of each semaphore (s1 to s4)
\*two variables for the position of the switches (sw1 and sw2).
VARIABLES t1, t2, s1, s2, s3, s4, sw1, sw2

Init == /\ t1 = "TRACK1"
        /\ t2 = "TRACK4"
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
\* Termination Property
CrossingSuccessful == <>Train1Crossed /\ <>Train2Crossed

(*
John Gall "A complex system that works is invariably found to have evolved from a simple system that worked."
-> begin with the simplest behavior possible
*)

\* First: Move Train 1 in a straight line
\* Second: To prevent the collisions, add the condition for s1 and s2
\* Third: To order the switches, but make simplifier, set if-else for MoveT2
\* Fourth: To prevent the collisions initialize the semaphores.
MoveT1 == /\ \/ /\ t1 = "TRACK1"
                /\ s1 = "GO" \* add the condition to prevent from collisions
                /\ t1' = "SWITCH1"
                /\ s1' = "STOP"
                /\ UNCHANGED s2
             \/ /\ t1 = "SWITCH1"
                /\ t1' = "TRACK2"
                /\ UNCHANGED <<s1, s2>>
             \/ /\ t1 = "TRACK2"
                /\ s2 = "GO" \* add the condition to prevent from collisions
                /\ t1' = "SWITCH2"
                /\ s2' = "STOP"
                /\ UNCHANGED s1
             \/ /\ t1 = "SWITCH2"
                /\ t1' = "TRACK4"
                /\ UNCHANGED <<s1, s2>>
          /\ UNCHANGED <<t2, s3, s4, sw1, sw2>>

\* Move Train 2 in a straight line
\* To prevent the collisions, add the condition for s1 and s2
MoveT2 == /\ \/ /\ t2 = "TRACK4"
                /\ s4 = "GO" \* add the condition to prevent from collisions
                /\ t2' = "SWITCH2"
                /\ s4' = "STOP"
                /\ UNCHANGED s3
             \/ /\ t2 = "SWITCH2"
                /\ t2' = IF sw2 = "STRAIGHT" THEN "TRACK2" ELSE "TRACK3"
                /\ UNCHANGED <<s3, s4>>
             \/ /\ t2 = "TRACK2"
                /\ s3 = "GO" \* add the condition to prevent from collisions
                /\ t2' = "SWITCH1"
                /\ s3' = "STOP"
                /\ UNCHANGED s4
             \/ /\ t2 = "TRACK3"
                /\ s3 = "GO" \* add the condition to prevent from collisions
                /\ t2' = "SWITCH1"
                /\ s3' = "STOP"
                /\ UNCHANGED s4
             \/ /\ t2 = "SWITCH1"
                /\ t2' = "TRACK1"
                /\ UNCHANGED <<s3, s4>>
          /\ UNCHANGED <<t1, s1, s2, sw1, sw2>>

\* To swith semaphores 1 and 2 from "STOP" to "GO", by naive way.
\* The following condition is not enough for trains to avoid collisions by the following reason:
\* 1. If Train 1 is on "TRACK1" and train 2 on "TRACK4", then each of semaphores s1 and s2 can be "GO".
\* 2. And then, there is no way to change from "GO" to "STOP" in the time.
\* 3. So, there comes a collision.
\* To prevent the above case, should initialize semaphore to Action MoveT1 and MoveT2
ChangeS1 == /\ t1 = "TRACK1" \* train 1 is waiting in front of the semaphore 1.
            /\ t2 \notin {"TRACK2", "SWITCH1"} \* train is not on the track that train 1 wants to enter
            /\ sw1 = "STRAIGHT"
            /\ s1' = "GO"
            /\ UNCHANGED <<t1, t2, s2, s3, s4, sw1, sw2>>

ChangeS2 == /\ t1 \in {"TRACK2", "TRACK3"} \* train 1 is waiting in front of the semaphore 2.
            /\ t2 \notin {"TRACK4", "SWITCH2"} \* train is not on the track that train 1 wants to enter
            /\ s2' = "GO"
            /\ UNCHANGED <<t1, t2, s1, s3, s4, sw1, sw2>>

\* To swith semaphore 4 from "STOP" to "GO"
ChangeS3 == /\ t2 \in {"TRACK2", "TRACK3"} \* train 1 is waiting in front of the semaphore 3.
            /\ t1 \notin {"TRACK1", "SWITCH1"} \* train is not on the track that train 1 wants to enter
            \* /\ sw2 = "STRAIGHT"
            /\ s3' = "GO"
            /\ UNCHANGED <<t1, t2, s1, s4, s2, sw1, sw2>>

ChangeS4 == /\ t2 = "TRACK4" \* train 1 is waiting in front of the semaphore 4.
            /\ t1 \notin {"TRACK3", "SWITCH2"} \* train is not on the track that train 1 wants to enter
            /\ sw2 = "RIGHT"
            /\ s4' = "GO"
            /\ UNCHANGED <<t1, t2, s1, s3, s2, sw1, sw2>>

\* To change the switches
\* semaphore should be "STOP" before change switches
\* If train is on switches, should not change the switches
\* If the oncoming train is on the track, should not change the switches to it.
ChangeSw1 == /\ s1 = "STOP"
             /\ s3 = "STOP"
             /\ t1 # "SWITCH1"
             /\ \/ /\ sw1 = "STRAIGHT"
                   /\ t2 # "TRACK3"
                   /\ t1 # "TRACK1" \* Only change switch one once track 1 is free
                   /\ sw1' = "LEFT"
                \/ /\ sw1 = "LEFT"
                   /\ t1 = "TRACK1"
                   /\ sw1' = "STRAIGHT"
             /\ UNCHANGED <<t1, t2, s1, s2, s3, s4, sw2>> 

ChangeSw2 == /\ s2 = "STOP"
             /\ s4 = "STOP"
             /\ t2 # "SWITCH2"
             /\ \/ /\ sw2 = "RIGHT"
                   /\ t1 # "TRACK2"
                   /\ t2 # "TRACK4"
                   /\ sw2' = "STRAIGHT"
                \/ /\ sw2 = "STRAIGHT"
                   /\ t2 = "TRACK4"
                   /\ sw2' = "RIGHT"
             /\ UNCHANGED <<t1, t2, s1, s2, s3, s4, sw1>> 

\* First Specification
vars == <<t1, t2, s1, s2, s3, s4, sw1, sw2>>
\* Next == MoveT1 \/ MoveT2
\* Add the action to change semaphores and to change switches
Next == \/ MoveT1 
        \/ MoveT2 
        \/ ChangeS1 
        \/ ChangeS2 
        \/ ChangeS3 
        \/ ChangeS4 
        \/ ChangeSw1 
        \/ ChangeSw2 
        \/ (Train1Crossed /\ Train2Crossed /\ UNCHANGED vars) \* To terminate and to prevent deadlock


Fairness == /\ WF_vars(MoveT1) 
            /\ WF_vars(MoveT2) 
            /\ WF_vars(ChangeS1) 
            /\ WF_vars(ChangeS2) 
            /\ WF_vars(ChangeS3) 
            /\ WF_vars(ChangeS4) 
            /\ WF_vars(ChangeSw1) 
            /\ WF_vars(ChangeSw2)  

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================
\* Modification History
\* Last modified Sat Jun 27 18:57:41 JST 2020 by daioh
\* Created Fri Jun 26 17:29:19 JST 2020 by daioh
