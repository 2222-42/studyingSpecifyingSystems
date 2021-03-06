------------------------------- MODULE Graphs -------------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

-----------------------------------------------------------------------------
IsDirectedGraph(G) ==
    /\ G = [node |-> G.node, edge |-> G.edge]
    /\ G.edge \subseteq (G.node \X G.node)

DirectedSubgraph(G) ==
    {H \in [node: SUBSET G.node, edge: SUBSET (G.node \X G.node)]:
        IsDirectedGraph(H) /\ H.edge \subseteq G.edge}

-----------------------------------------------------------------------------

IsUndirectedGraph(G) ==
    /\ IsDirectedGraph(G)
    /\ \A e \in G.edge : <<e[2], e[1]>> \in G.edge

UndirectedSubraph(G) ==
    {H \in DirectedSubgraph(G) : IsUndirectedGraph(H)}

-----------------------------------------------------------------------------
(*  Stephan suggests to redefine Seq as
UNION{[1..n -> S]: n \in 0..N} in the TLC model to avoid changing the
original spec.*)
Path(G) == 
    {p \in Seq(G.node): /\ p # <<>>
                        /\ \A i \in 1..(Len(p) - 1): <<p[i], p[i+1]>> \in G.edge }

AreConnectedIn(m, n, G) ==
    \E p \in Path(G): (p[1] = m /\ p[Len(p)] = n)

IsStronglyConnected(G) ==
    \A m, n \in G.node : AreConnectedIn(m, n, G)

-----------------------------------------------------------------------------

IsTreeWithRoot(G, r) ==
    /\ IsDirectedGraph(G)
    /\ \E e \in G.edge: /\ e[1] # r
                        /\ \A f \in G.edge : (e[1] = f[1]) => (e = f)
    /\ \A n \in G.node: AreConnectedIn(n, r, G)
=============================================================================
\* Modification History
\* Created Sun Apr 19 13:18:18 JST 2020 by daioh
