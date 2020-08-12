------------------------ MODULE NewLinearSnapshotPS ------------------------
EXTENDS NewLinearSnapshot

Pi == Nat \ {0}
Dom == {r \in Readers : rstate[r] # <<>>}
INSTANCE Prophecy WITH DomPrime <- Dom'

IEndRd(i,j) == /\ interface[i] = NotMemVal
               /\ interface' = [interface EXCEPT ![i] = rstate[i][j]]
               /\ rstate' = [rstate EXCEPT ![i] = <<>>]
               /\ UNCHANGED <<mem, wstate>>

Nxt == \/ \E i \in Readers: \/ BeginRd(i) 
                            \/ \E j \in 1..Len(rstate[i]): IEndRd(i, j)
       \/ \E i \in Writers: \/ \E cmd \in RegVals : BeginWr(i, cmd)
                            \/ DoWr(i) \/ EndWr(i)

THEOREM  Next = Nxt
BY DEF Next, Nxt, EndRd, IEndRd

PredBeginRd(p) == TRUE
PredDomBeginRd == {}
DomInjBeginRd == IdFcn(Dom)

PredIEndRd(p, i, j) == j = p[i]
PredDomIEndRd(i) == {i}
DomInjIEndRd == IdFcn(Dom')

PredBeginWr(p) == TRUE
PredDomBeginWr == {}
DomInjBeginWr == IdFcn(Dom)

PredDoWr(p) == TRUE
PredDomDoWr == {}
DomInjDoWr == IdFcn(Dom)

PredEndWr(p) == TRUE
PredDomEndWr == {}
DomInjEndWr == IdFcn(Dom)

Condition ==
    [][/\ \A i \in Readers:
                /\ ProphCondition(BeginRd(i), DomInjBeginRd, PredDomBeginRd, PredBeginRd)
                /\ \A j \in 1..Len(rstate[i]):
                        ProphCondition(IEndRd(i,j), DomInjIEndRd, PredDomIEndRd(i), 
                                       LAMBDA p : PredIEndRd(p,i,j))
       /\ \A i \in Writers:
                /\ \A cmd \in RegVals:
                    ProphCondition(BeginWr(i, cmd), DomInjBeginWr, PredDomBeginWr, PredBeginWr)
                /\ ProphCondition(DoWr(i), DomInjDoWr, PredDomDoWr, PredDoWr)
                /\ ProphCondition(EndWr(i), DomInjEndWr, PredDomEndWr, PredEndWr)
      ]_vars


---------------------------------------------------------------

VARIABLE p
varsP == <<vars, p>>

InitP == Init /\ (p = EmptyFcn)

BeginRdP(i) == ProphAction(BeginRd(i),p,p', DomInjBeginRd, PredDomBeginRd, PredBeginRd)
BeginWrP(i, cmd) == ProphAction(BeginWr(i, cmd),p,p', DomInjBeginWr, PredDomBeginWr, PredBeginWr)
DoWrP(i) == ProphAction(DoWr(i),p,p', DomInjDoWr, PredDomDoWr, PredDoWr)
IEndRdP(i,j) == ProphAction(IEndRd(i,j),p,p', DomInjIEndRd, PredDomIEndRd(i), LAMBDA q: PredIEndRd(q,i,j))
EndWrP(i) == ProphAction(EndWr(i),p,p', DomInjEndWr, PredDomEndWr, PredEndWr)


NextP == \/ \E i \in Readers : \/ BeginRdP(i)
                               \/ \E j \in 1..Len(rstate[i]): IEndRdP(i,j)
         \/ \E i \in Writers : \/ \E cmd \in RegVals : \/ BeginWrP(i,cmd) 
                               \/ DoWrP(i) \/ EndWrP(i)

SpecP == InitUP /\ [][NextP]_varsP

THEOREM SpecP => [][\A i \in Readers : BeginRdP(i) => (IF p'[i] = 1 THEN 1 else 0) \in {0,1}]_varsP

THEOREM SpecP => [][\A i \in Writers, cmd \in RegVals : 
                        DoWrP(i) => 
                            {j \in Readers : (rstate[j] # <<>> /\ (p[j] = Len(rstate'[j]))) } \in (SUBSET Readers)]_varsP

---------------------------------------------------------------


VARIABLE s
varsPS == <<vars, p, s>>

INSTANCE Stuttering WITH vars <- varsP

InitPS == InitP /\ (p = EmptyFcn)

BeginRdPS(i) == MayPostStutter(BeginRdP(i),"BeginRd",i,0, 
                               IF p'[i] = 1 THEN 1 ELSE 0, LAMBDA j: j -1)
ASSUME StutterConstantCondition({0,1}, 0, LAMBDA j: j - 1)
BeginWrPS(i, cmd) == NoStutter(BeginWrP(i, cmd))
DoWrPS(i) == MayPostStutter(DoWrP(i),"DoWr",i,{}, 
                            {j \in Readers: (rstate[j] # <<>>) /\ (p[j] = Len(rstate'[j]))}, 
                            LAMBDA S: S\{CHOOSE x \in S : TRUE})
ASSUME StutterConstantCondition(SUBSET {Readers}, {}, LAMBDA S: S\{CHOOSE x \in S : TRUE})
IEndRdPS(i,j) == NoStutter(IEndRdP(i,j))
EndWrPS(i) == NoStutter(EndWrP(i))


NextPS == \/ \E i \in Readers : \/ BeginRdPS(i)
                                \/ \E j \in 1..Len(rstate[i]): IEndRdPS(i,j)
          \/ \E i \in Writers : \/ \E cmd \in RegVals : \/ BeginWrPS(i,cmd) 
                                \/ DoWrPS(i) \/ EndWrPS(i)

SafeSpecPS == InitPS /\ [][NextPS]|varsPS
SpecPS == SafeSpecPS /\ Fairness

=============================================================================
\* Modification History
\* Last modified Tue Aug 11 16:21:48 JST 2020 by daioh
\* Created Tue Aug 11 10:17:22 JST 2020 by daioh
