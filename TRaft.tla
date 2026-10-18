--------------------------------- MODULE TRaft ---------------------------------
(* TRaft, revised protocol (Sept 2026 revision plan):
   - out-of-order physical receipt into slots (holes allowed), durable frontier
     F = longest gap-free prefix; elections and ACKs use only the frontier;
   - prefix-ordered, per-entry commitment with Raft's current-term rule;
   - rule 1: a term never continues a partition of an earlier term (new leader
     opens a fresh partition with a no-op);
   - rule 2: on any term change a node discards every slot beyond its frontier;
   - C1: a partition is identified by (term, rho); a stale one is truncated;
   - C2: the first entry of partition rho is accepted only if the local
     partition rho-1 has the announced term (prevTerm) and size (prevSize).
   CheckC1C2 = FALSE gives the design with rules 1+2 only (known unsafe).
   Structure follows Ongaro's raft.tla; messages are a set (loss/dup/reorder). *)
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Server, Nil, Theta, MaxTerm, MaxIndex, MaxMsgs, CheckC1C2, UseRule2, MaxRestarts

Follower == "Follower"
Candidate == "Candidate"
Leader == "Leader"
RVReq == "RVReq"
AEReq == "AEReq"
AEResp == "AEResp"

VARIABLES messages, currentTerm, state, votedFor, slots, commitIndex,
          votesGranted, matchIndex, committed, restarts
vars == <<messages, currentTerm, state, votedFor, slots, commitIndex,
          votesGranted, matchIndex, committed, restarts>>

Index == 1..MaxIndex
Quorum == (Cardinality(Server) \div 2) + 1
Perms == Permutations(Server)

Max(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Min2(a, b) == IF a <= b THEN a ELSE b

Send(m) == messages' = messages \cup {m}
SendSet(M) == messages' = messages \cup M

\* ---- slot geometry -----------------------------------------------------
Frontier(s) == Max({k \in Index : \A m \in 1..k : s[m] # Nil})
PartIdx(s, r) == {k \in Index : s[k] # Nil /\ s[k].rho = r}
PartExists(s, r) == PartIdx(s, r) # {}
FirstIdx(s, r) == Min(PartIdx(s, r))
PartTerm(s, r) == s[FirstIdx(s, r)].term
PartSize(s, r) == Cardinality(PartIdx(s, r))
RhoFPlus1(s) == IF Frontier(s) = 0 THEN 0 ELSE s[Frontier(s)].rho + 1
TruncFrom(s, k) == [m \in Index |-> IF m >= k THEN Nil ELSE s[m]]
Purge(s) == IF UseRule2 THEN TruncFrom(s, Frontier(s) + 1) ELSE s
Key(s) == IF Frontier(s) = 0 THEN <<0, 0, 0>>
          ELSE <<s[Frontier(s)].term, s[Frontier(s)].rho, s[Frontier(s)].sigma>>
KeyLE(a, b) == \/ a[1] < b[1]
               \/ (a[1] = b[1] /\ a[2] < b[2])
               \/ (a[1] = b[1] /\ a[2] = b[2] /\ a[3] <= b[3])

\* ---- init ---------------------------------------------------------------
Init == /\ messages = {}
        /\ currentTerm = [i \in Server |-> 0]
        /\ state = [i \in Server |-> Follower]
        /\ votedFor = [i \in Server |-> Nil]
        /\ slots = [i \in Server |-> [k \in Index |-> Nil]]
        /\ commitIndex = [i \in Server |-> 0]
        /\ votesGranted = [i \in Server |-> {}]
        /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
        /\ committed = [k \in Index |-> Nil]
        /\ restarts = 0

\* ---- crash / election ---------------------------------------------------
Restart(i) ==
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ commitIndex' = [commitIndex EXCEPT ![i] = 0]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ UNCHANGED <<messages, currentTerm, votedFor, slots, committed>>

Timeout(i) ==                                  \* AdoptTerm(currentTerm+1) + self vote
    /\ state[i] \in {Follower, Candidate}
    /\ currentTerm[i] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ slots' = [slots EXCEPT ![i] = Purge(slots[i])]                 \* rule 2
    /\ UNCHANGED <<messages, commitIndex, matchIndex, committed>>

RequestVote(i, j) ==
    /\ state[i] = Candidate /\ j # i
    /\ Send([mtype |-> RVReq, mterm |-> currentTerm[i], mkey |-> Key(slots[i]),
             msource |-> i, mdest |-> j])
    /\ UNCHANGED <<currentTerm, state, votedFor, slots, commitIndex,
                   votesGranted, matchIndex, committed>>

BecomeLeader(i) ==                             \* OnElected
    /\ state[i] = Candidate
    /\ Cardinality(votesGranted[i]) >= Quorum
    /\ LET s == Purge(slots[i])
           F == Frontier(s)
           noop == IF F = 0
                   THEN [term |-> currentTerm[i], rho |-> 0, sigma |-> 1,
                         prevTerm |-> 0, prevSize |-> 0]
                   ELSE [term |-> currentTerm[i], rho |-> s[F].rho + 1, sigma |-> 1,
                         prevTerm |-> s[F].term, prevSize |-> PartSize(s, s[F].rho)]
       IN /\ F < MaxIndex
          /\ slots' = [slots EXCEPT ![i] = [s EXCEPT ![F + 1] = noop]]
          /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> IF j = i THEN F + 1 ELSE 0]]
    /\ state' = [state EXCEPT ![i] = Leader]
    /\ UNCHANGED <<messages, currentTerm, votedFor, commitIndex, votesGranted, committed>>

\* ---- leader: ingestion and replication ----------------------------------
ClientRequest(i, newPart) ==                   \* newPart: the timestamp is non-monotone
    /\ state[i] = Leader
    /\ LET s == slots[i]
           F == Frontier(s)
           r == s[F].rho
           np == newPart \/ PartSize(s, r) = Theta
           e == IF np
                THEN [term |-> currentTerm[i], rho |-> r + 1, sigma |-> 1,
                      prevTerm |-> s[F].term, prevSize |-> PartSize(s, r)]
                ELSE [term |-> currentTerm[i], rho |-> r, sigma |-> PartSize(s, r) + 1,
                      prevTerm |-> IF r = 0 THEN 0 ELSE PartTerm(s, r - 1),
                      prevSize |-> IF r = 0 THEN 0 ELSE PartSize(s, r - 1)]
       IN /\ F < MaxIndex
          /\ slots' = [slots EXCEPT ![i] = [s EXCEPT ![F + 1] = e]]
    /\ UNCHANGED <<messages, currentTerm, state, votedFor, commitIndex,
                   votesGranted, matchIndex, committed>>

AppendEntries(i, j, k) ==                      \* any entry, any time: scheduling, speculation, resend
    /\ state[i] = Leader /\ j # i
    /\ k \in 1..Frontier(slots[i])
    /\ Send([mtype |-> AEReq, mterm |-> currentTerm[i], mindex |-> k,
             mentry |-> slots[i][k], msource |-> i, mdest |-> j])
    /\ UNCHANGED <<currentTerm, state, votedFor, slots, commitIndex,
                   votesGranted, matchIndex, committed>>

AdvanceCommitIndex(i) ==                       \* prefix commitment + current-term rule
    /\ state[i] = Leader
    /\ LET F == Frontier(slots[i])
           Agree(k) == {i} \cup {j \in Server : matchIndex[i][j] >= k}
           agreeIdx == {k \in 1..F : Cardinality(Agree(k)) >= Quorum}
           newC == Max({k \in agreeIdx : slots[i][k].term = currentTerm[i]})
       IN /\ newC > commitIndex[i]
          /\ commitIndex' = [commitIndex EXCEPT ![i] = newC]
          /\ committed' = [k \in Index |-> IF committed[k] = Nil /\ k <= newC
                                            THEN [entry |-> slots[i][k], cterm |-> currentTerm[i]]
                                            ELSE committed[k]]
    /\ UNCHANGED <<messages, currentTerm, state, votedFor, slots, votesGranted, matchIndex>>

LearnCommit(i, j) ==                           \* NotifyCommit(c, t_c) with identity check
    /\ i # j /\ state[j] = Leader /\ currentTerm[i] = currentTerm[j]
    /\ LET c == commitIndex[j]
       IN /\ c > commitIndex[i]
          /\ slots[i][c] # Nil /\ slots[i][c].term = slots[j][c].term
          /\ commitIndex' = [commitIndex EXCEPT ![i] = c]
    /\ UNCHANGED <<messages, currentTerm, state, votedFor, slots, votesGranted, matchIndex, committed>>

\* ---- message handlers ---------------------------------------------------
UpdateTerm(i, j, m) ==                         \* AdoptTerm
    /\ m.mterm > currentTerm[i]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ slots' = [slots EXCEPT ![i] = Purge(slots[i])]                 \* rule 2
    /\ UNCHANGED <<messages, commitIndex, votesGranted, matchIndex, committed>>

HandleRequestVoteRequest(i, j, m) ==
    LET grant == /\ m.mterm = currentTerm[i]
                 /\ KeyLE(Key(slots[i]), m.mkey)
                 /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ votedFor' = IF grant THEN [votedFor EXCEPT ![i] = j] ELSE votedFor
       /\ votesGranted' = IF grant /\ state[j] = Candidate /\ currentTerm[j] = m.mterm
                          THEN [votesGranted EXCEPT ![j] = votesGranted[j] \cup {i}]
                          ELSE votesGranted                 \* vote delivered directly
       /\ UNCHANGED <<messages, currentTerm, state, slots, commitIndex, matchIndex, committed>>

HandleAppendEntriesRequest(i, j, m) ==         \* Algorithm 4
    /\ m.mterm = currentTerm[i]
    /\ LET e  == m.mentry
           k  == m.mindex
           s0 == slots[i]
           \* C1: partition identity is (term, rho)
           s1 == IF CheckC1C2 /\ PartExists(s0, e.rho) /\ PartTerm(s0, e.rho) # e.term
                 THEN TruncFrom(s0, FirstIdx(s0, e.rho)) ELSE s0
           \* C2: entering partition e.rho
           needC2 == e.rho > 0 /\ ~PartExists(s1, e.rho)
           okAhead == e.rho <= RhoFPlus1(s1)
           prevOK == PartExists(s1, e.rho - 1)
           termOK == ~CheckC1C2 \/ (prevOK /\ PartTerm(s1, e.rho - 1) = e.prevTerm)
           surplus == prevOK /\ PartSize(s1, e.rho - 1) > e.prevSize
           s2 == IF needC2 /\ CheckC1C2 /\ okAhead /\ termOK /\ surplus
                 THEN TruncFrom(s1, FirstIdx(s1, e.rho - 1) + e.prevSize) ELSE s1
           sizeOK == prevOK /\ PartSize(s2, e.rho - 1) = e.prevSize
           accept == ~needC2 \/ (okAhead /\ termOK /\ sizeOK)
           \* per-slot identity check, then store
           s3 == IF s2[k] # Nil /\ s2[k].term # e.term THEN TruncFrom(s2, k) ELSE s2
           s4 == [s3 EXCEPT ![k] = e]
           Fold == Frontier(s3)
           Fnew == Frontier(s4)
       IN IF accept
          THEN /\ slots' = [slots EXCEPT ![i] = s4]
               /\ IF Fnew > Fold
                  THEN Send([mtype |-> AEResp, mterm |-> currentTerm[i], mindex |-> Fnew,
                             mentryTerm |-> s4[Fnew].term, msource |-> i, mdest |-> j])
                  ELSE UNCHANGED messages
          ELSE /\ slots' = [slots EXCEPT ![i] = s2]
               /\ UNCHANGED messages
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, votesGranted, matchIndex, committed>>

HandleAppendEntriesResponse(i, j, m) ==        \* Algorithm 3, identity-checked ACK
    /\ m.mterm = currentTerm[i]
    /\ state[i] = Leader
    /\ slots[i][m.mindex] # Nil /\ slots[i][m.mindex].term = m.mentryTerm
    /\ m.mindex > matchIndex[i][j]
    /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mindex]
    /\ UNCHANGED <<messages, currentTerm, state, votedFor, slots, commitIndex, votesGranted, committed>>

Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \/ UpdateTerm(i, j, m)
       \/ (m.mtype = RVReq /\ HandleRequestVoteRequest(i, j, m))
       \/ (m.mtype = AEReq /\ HandleAppendEntriesRequest(i, j, m))
       \/ (m.mtype = AEResp /\ HandleAppendEntriesResponse(i, j, m))

Next == \/ (\E i \in Server : Restart(i)) /\ restarts < MaxRestarts /\ restarts' = restarts + 1
        \/ /\ UNCHANGED restarts
           /\ \/ \E i \in Server : Timeout(i)
              \/ \E i, j \in Server : RequestVote(i, j)
              \/ \E i \in Server : BecomeLeader(i)
              \/ \E i \in Server, b \in BOOLEAN : ClientRequest(i, b)
              \/ \E i, j \in Server, k \in Index : AppendEntries(i, j, k)
              \/ \E i \in Server : AdvanceCommitIndex(i)
              \/ \E i, j \in Server : LearnCommit(i, j)
              \/ \E m \in messages : Receive(m)

Spec == Init /\ [][Next]_vars

StateConstraint == Cardinality(messages) <= MaxMsgs

\* ---- properties ---------------------------------------------------------
ElectionSafety ==
    \A i, j \in Server : (i # j /\ state[i] = Leader /\ state[j] = Leader)
        => currentTerm[i] # currentTerm[j]

LogMatching ==                                  \* over durable frontiers
    \A i, j \in Server : \A k \in 1..Min2(Frontier(slots[i]), Frontier(slots[j])) :
        slots[i][k].term = slots[j][k].term => \A m \in 1..k : slots[i][m] = slots[j][m]

LeaderCompleteness ==                           \* leaders of terms >= the commit term hold every committed entry
    \A i \in Server : state[i] = Leader =>
        \A k \in Index : (committed[k] # Nil /\ currentTerm[i] >= committed[k].cterm)
            => slots[i][k] = committed[k].entry

StateMachineSafety ==                           \* applied prefix = committed prefix
    \A i \in Server : \A k \in 1..Min2(commitIndex[i], Frontier(slots[i])) :
        committed[k] # Nil /\ slots[i][k] = committed[k].entry

SingleTermPartition ==                          \* rule 1 + C1
    \A i \in Server : \A r \in 0..MaxIndex :
        \A k1, k2 \in PartIdx(slots[i], r) : slots[i][k1].term = slots[i][k2].term
================================================================================
