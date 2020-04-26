---------------------------- MODULE BNFGrammars ----------------------------
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals
----------------------------------------------------------
Grammar == [STRING -> SUBSET Seq(STRING)]

tok(s) == {<<s>>}
Tok(S) == {<<s>> : s \in S}
\*op == tok("+") | tok("-") | tok("*") | tok("/")

\* Letter == {"a", "b", ..., "z"}
OneOf(s) == {<<s[i]>>: i \in DOMAIN s}
\* Letter == OneOf("abcd..z")
----------------------------------------------------------

Nil == {<<>>}
L & M == { s \o t : s \in L, t \in M}
L | M == L \cup M
L^+ == LET LL[n \in Nat] ==
            IF n = 0 THEN L
                     ELSE LL[n - 1] | LL[n - 1] & L
       IN UNION {LL[n] : n \in Nat}
L^* == Nil | L^+

----------------------------------------------------------
L ::= M == L = M

LestGrammer(P(_)) ==
    CHOOSE G \in Grammar :
        /\ P(G)
        /\ \A H \in Grammar  : P(H) => (\A s \in STRING : G[s] \subseteq H[s])

GSE == LET op == Tok({"+", "-", "*", "/"})
           ident == Tok(OneOf("abcdefdhijklmnopqrstuvwxyz"))
           P(G) == /\ G.def ::= ident & tok("==") & G.expr
                   /\ G.expr ::=      ident
                                    | G.expr & op & G.expr
                                    | tok("(") & G.expr & tok(")")
                                    | tok("LET") & G.def & tok("IN") & G.expr
       IN LestGrammer(P)


=============================================================================
\* Modification History
\* Created Sun Apr 26 11:17:25 JST 2020 by daioh
