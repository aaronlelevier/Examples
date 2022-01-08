-------------------------- MODULE MemoryInterface --------------------------
\* Memory Interface from pg. 45-48  

VARIABLE memInt

CONSTANT Send(_,_,_,_),
         Reply(_,_,_,_),
         InitMemInt,
         Proc,
         Adr,
         Val

\* document the allowed values for Send/Reply constant action params
ASSUME \A p, d, miOld, miNew:
  /\ Send(p, d, miOld, miNew) \in BOOLEAN
  /\ Reply(p, d, miOld, miNew) \in BOOLEAN

\* the set of all messages
MReq == [op: {"Rd"}, adr: Adr] \cup [op: {"Wr"}, adr: Adr, val: Val]

\* prefer constant expressions as opposed to extra args
NoVal == CHOOSE x : x \notin Val

=============================================================================
\* Modification History
\* Last modified Sat Jan 08 08:47:58 PST 2022 by aaron
\* Created Sat Jan 08 08:40:14 PST 2022 by aaron
