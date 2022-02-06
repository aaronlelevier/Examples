-------------------------------- MODULE RTOP --------------------------------
CONSTANT P, \* P is the set of Principals
         R  \* R is the set of Resources

VARIABLE ptor, rtop

vars == <<ptor, rtop>>

TypeOK  ==  /\ ptor \in [P -> SUBSET R]
            /\ rtop \in [R -> SUBSET P]

Init ==
    /\ ptor = [p \in P |-> (CHOOSE r \in SUBSET R: TRUE)]
    /\ rtop = [r \in R |-> {p \in P : r \in ptor[p]}]
-----------------------------------------------------------------------------

\* p gains access to r
PAddR(p, r) ==
    /\ ptor' = [ptor EXCEPT ![p] = @ \cup {r}]
    /\ rtop' = [rtop EXCEPT ![r] = @ \cup {p}]

\* p loses access to r
PRemoveR(p, r) ==
    /\ ptor' = [ptor EXCEPT ![p] = @ \ {r}]
    /\ rtop' = [rtop EXCEPT ![r] = @ \ {p}]
-----------------------------------------------------------------------------

\* new r is added and a subset of P will have access to r
RAdded(r) ==
    /\ rtop[r] = {} \* removed r's have an empty mapping
                    \* r must have been removed to add it
    /\ rtop' = [rtop EXCEPT ![r] = (CHOOSE p \in SUBSET P: TRUE)]
    /\ IF rtop[r] # {}
        THEN \A p \in rtop[r]:
            ptor' = [ptor EXCEPT ![p] = @ \cup {r}]
        ELSE ptor' = ptor

\* r is removed
RRemoved(r) ==
    /\ rtop' = [rtop EXCEPT ![r] = {}]
    /\ \A p \in P:
        ptor' = [ptor EXCEPT ![p] = @ \ {r}]
-----------------------------------------------------------------------------
Next ==
    \/ \E p \in P, r \in R:
        \/ PAddR(p, r) \/ PRemoveR(p, r)
    \/ \E r \in R:
        \/ RAdded(r) \/ RRemoved(r)

Spec == Init /\ [][Next]_<<vars>>
-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
=============================================================================
\* Modification History
\* Last modified Sun Feb 06 08:03:13 PST 2022 by aaron
\* Created Sat Jan 22 09:52:31 PST 2022 by aaron
