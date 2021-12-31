------------------------------ MODULE Removal ------------------------------

EXTENDS Integers, Sequences

Remove(i, seq) == 
  [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] 
                                      ELSE seq[j+1]]

=============================================================================
\* Modification History
\* Last modified Thu Dec 30 09:12:36 PST 2021 by aaron
\* Created Thu Dec 30 09:12:27 PST 2021 by aaron
