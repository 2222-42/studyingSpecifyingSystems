-------------------------- MODULE AfekSimplifiedH --------------------------
EXTENDS AfekSimplified, Sequences

VARIABLE h
varsH == <<vars, h>>

InitH == Init /\ (h = [i \in Readers |-> <<>>])
memBar == [i \in Writers |-> imem[i][1]]

BeginWrH(i,cmd) == BeginWr(i, cmd) /\ (h' = h)

DoWrH(i) == /\ DoWr(i) 
            /\ h' = [j \in Readers |-> 
                        IF h[j] = <<>>
                            THEN <<>>
                            ELSE Append(h[j], memBar')]

EndWrH(i) == EndWr(i) /\ (h' = h)
BeginRdH(i) == /\ BeginRd(i)
               /\ h' = [h EXCEPT ![i] = <<memBar>>]
Rd1H(i) == Rd1(i) /\ (h' = h)
Rd2H(i) == Rd2(i) /\ (h' = h)
TryEndRdH(i) == /\ TryEndRd(i) 
                /\ h' = IF rdVal1[i] = rdVal2[i]
                            THEN [h EXCEPT ![i] = <<>>]
                            ELSE h

NextH == \/ \E i \in Readers: BeginRdH(i) \/ Rd1H(i) \/ Rd2H(i) \/ TryEndRdH(i)
         \/ \E i \in Writers: \/ \E cmd \in RegVals: BeginWrH(i, cmd) 
                              \/ DoWrH(i) \/ EndWrH(i)

SpecH == InitH /\ [][NextH]_varsH

wstateBar == [i \in Writers |-> 
                IF (interface[i] = NotRegVal) \/ (wrNum[i] = imem[i][2])
                    THEN NotRegVal
                    ELSE interface[i]
             ]

NLS == INSTANCE NewLinearSnapshot WITH mem <- memBar, rstate <- h, wstate <- wstateBar

THEOREM SpecH => NLS!SafeSpec
=============================================================================
\* Modification History
\* Last modified Wed Aug 12 16:48:44 JST 2020 by daioh
\* Created Wed Aug 12 16:07:35 JST 2020 by daioh
