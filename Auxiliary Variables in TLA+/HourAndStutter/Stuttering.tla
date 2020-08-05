----------------------------- MODULE Stuttering -----------------------------

top == [top |-> "top"]

(* the components of s are
id: An identier to distinguish that action A from other actions to which stuttering steps are added.
*)
VARIABLES  s, vars

\* A: The action to which stuttering steps are being added.
NoStutter(A) == (s = top) /\ A /\ (s' = s)

\* context: The tuple of context identiers of A. This component may be used in defining refinement mappings
\* bot: The smallest element of Sigma.
\* initVal: 
\* decr:

PostStutter(A, actionId, context, bot, initVal, decr(_)) ==
    IF s = top THEN /\ A 
                    /\ s' = [id |-> actionId, ctxt |-> context, val |-> initVal]
               ELSE /\ s.id = actionId
                    /\ UNCHANGED vars
                    /\ s' = IF s.val = bot THEN top 
                                           ELSE [s EXCEPT !.val = decr(s.val)]

\* enabled: A formula that should be equivalent to enabled A.
PreStutter(A, enabled, actionId, context, bot, initVal, decr(_)) ==
    IF s = top 
        THEN /\ enabled
             /\ UNCHANGED vars
             /\ s' = [id |-> actionId, ctxt |-> context, val |-> initVal]
        ELSE /\ s.id = actionId
             /\ IF s.val = bot THEN /\ s.ctxt = context
                                    /\ A
                                    /\ s' = top 
                               ELSE /\ UNCHANGED vars
                                    /\ s' = [s EXCEPT !.val = decr(s.val)]

MayPostStutter(A, actionId, context, bot, initVal, decr(_)) ==
    IF s = top THEN /\ A 
                    /\ s' = IF initVal = bot
                            THEN s
                            ELSE [id |-> actionId, ctxt |-> context, val |-> initVal]
               ELSE /\ s.id = actionId
                    /\ UNCHANGED vars
                    /\ s' = IF decr(s.val) = bot THEN top 
                                           ELSE [s EXCEPT !.val = decr(s.val)]    

MayPreStutter (A, enabled, actionId, context, bot, initVal, decr(_)) ==
    IF s = top 
        THEN /\ enabled
             /\ IF initVal = bot
                THEN A /\ (s' = s)
                ELSE /\ UNCHANGED vars
                     /\ s' = [id |-> actionId, ctxt |-> context, val |-> decr(initVal)]
        ELSE /\ s.id = actionId
             /\ IF s.val = bot THEN /\ s.ctxt = context
                                    /\ A
                                    /\ s' = top 
                               ELSE /\ UNCHANGED vars
                                    /\ s' = [s EXCEPT !.val = decr(s.val)]





=============================================================================
\* Modification History
\* Created Wed Aug 05 10:27:28 JST 2020 by daioh
