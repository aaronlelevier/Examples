-------------------------------- MODULE RTOP --------------------------------
CONSTANT P, R

VARIABLE ptor, rtop

vars == <<ptor, rtop>>

TypeOK  ==  /\ ptor \in [P -> SUBSET R]
            /\ rtop \in [R -> SUBSET P]

Init ==
    /\ ptor = [p \in P |-> (CHOOSE r \in SUBSET R: TRUE)]
    /\ rtop = [r \in R |-> {p \in P : r \in ptor[p]}]

PAddR(p, r) ==
    /\ ptor' = [ptor EXCEPT ![p] = @ \cup {r}]
    /\ UNCHANGED <<rtop>>

Next ==
    \/ \E p \in P, r \in R:
        \/ PAddR(p, r)

Spec == Init /\ [][Next]_<<vars>>
-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
=============================================================================
\* Modification History
\* Last modified Sun Jan 23 11:10:52 PST 2022 by aaron
\* Created Sat Jan 22 09:52:31 PST 2022 by aaron
