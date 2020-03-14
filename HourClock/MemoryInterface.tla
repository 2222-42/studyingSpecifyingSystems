-------------------------- MODULE MemoryInterface --------------------------

VARIABLES memInt

CONSTANTS   Send(_, _, _, _),
            Reply(_, _, _, _),
            InitMemInt,
            Proc,
            Adr,
            Val


ASSUME \A p, d, miOld, miNew: /\ Send(p, d, miOld, miNew) \in BOOLEAN 
                              /\ Reply(p, d, miOld, miNew) \in BOOLEAN   

----------------------------------

MReq ==
    [op: {"Rd"}, adr: Adr] \union [op: {"Wr"}, adr: Adr, val: Val]

NoVal ==
    CHOOSE v: v \notin Val


=============================================================================
\* Modification History
\* Created Sun Feb 02 15:03:35 JST 2020 by daioh
