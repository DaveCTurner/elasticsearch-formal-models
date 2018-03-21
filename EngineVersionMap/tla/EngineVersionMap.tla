-------------------------- MODULE EngineVersionMap --------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

(* Actions on the Lucene index *)
CONSTANTS Lucene_addDocuments, Lucene_updateDocuments, Lucene_deleteDocuments

CONSTANTS ADD, RETRY_ADD, UPDATE, DELETE, NULL
CONSTANTS OPEN, CLOSED

CONSTANTS DocContent

CONSTANTS DocAutoIdTimestamp

(* We model the activity of a single document, since distinct documents
   (according to their IDs) are independent. Also each indexing operation
   occurs under a lock for that document ID, so there is not much concurrency
   to consider. *)


(* The set of individual requests that can occur on the document *)
Request(request_count)
    (* ADD: An optimised append-only write can only occur as the first operation
    on the document ID in seqno order. Any subsequent attempts to ADD the
    document have the retry flag set and modelled as a RETRY_ADD. *)
    ==    { [type |-> ADD, seqno |-> 1, content |-> content, autoIdTimeStamp |-> DocAutoIdTimestamp]
          : content \in DocContent
          }
    (* RETRY_ADD: A retry of a write that does involve an internally-generated
       document ID. *)
    \cup  { [type |-> RETRY_ADD, seqno |-> seqno, content |-> content, autoIdTimeStamp |-> DocAutoIdTimestamp]
          : seqno   \in 1..request_count
          , content \in DocContent
          }
    (* UPDATE: A write that does not involve an internally-generated document ID.
       RETRY_ADD: A retry of a write that does involve an internally-generated
       document ID.
       Both can occur at any seqno. *)
    \cup  { [type |-> UPDATE, seqno |-> seqno, content |-> content]
          : seqno   \in 1..request_count
          , content \in DocContent
          }
    (* DELETE *)
    \cup  { [type |-> DELETE, seqno |-> seqno]
          : seqno \in 1..request_count
          }

(* The set of sets of requests, which have distinct seqnos *)
RequestSet(request_count)
    == { rs \in SUBSET Request(request_count):
                /\ Cardinality(rs)                   = request_count
                /\ Cardinality({r.seqno : r \in rs}) = request_count
                /\ Cardinality({r.content: r \in rs /\ FALSE}) <= 1
       }

(* Apply a set of operations to a document in seqno order *)
RECURSIVE ApplyOps(_, _, _)
ApplyOps(requests, nextSeqno, currentContent)
    == IF   \A r \in requests: r.seqno < nextSeqno
       THEN currentContent
       ELSE LET r == CHOOSE r \in requests: r.seqno = nextSeqno
            IN IF r \in requests /\ r.seqno = nextSeqno
               THEN ApplyOps(requests, nextSeqno + 1,
                        CASE r.type = DELETE    -> NULL
                          [] r.type = ADD       -> r.content
                          [] r.type = RETRY_ADD -> r.content
                          [] r.type = UPDATE    -> r.content)
               ELSE Assert(FALSE, "Bad sequence")

(* Calculate the final doc by applying all the requests in order *)
FinalDoc(requests) == ApplyOps(requests, 1, NULL)

(* Apply each the operation in the Lucene buffer, rejecting an
   addDocuments when there is already a document present as this
   would lead to duplication. *)
RECURSIVE ApplyBufferedOperations(_, _)
ApplyBufferedOperations(buffer, origDoc)
    == IF buffer = <<>>
       THEN origDoc
       ELSE LET prevDoc == ApplyBufferedOperations(Tail(buffer), origDoc)
         IN LET nextOp  == Head(buffer)
         IN CASE       nextOp.type = Lucene_deleteDocuments -> NULL
              [] \/    nextOp.type = Lucene_updateDocuments
                 \/ /\ nextOp.type = Lucene_addDocuments
                    /\ prevDoc = NULL                       -> nextOp.content
              [] OTHER -> Assert(FALSE, "Error: Lucene_addDocuments when prevDoc /= NULL")

(* --algorithm basic

variables
    request_count \in 1..4,
    replication_requests \in RequestSet(request_count),
    expected_doc = FinalDoc(replication_requests),
    maxUnsafeAutoIdTimestamp \in {0, DocAutoIdTimestamp - 1, DocAutoIdTimestamp, DocAutoIdTimestamp + 1}

process LuceneProcess = "ReplicaLucene"
variables
    lucene =
        [ document |-> NULL
        , buffer   |-> <<>>
        , state    |-> OPEN
        ],
begin
    LuceneLoop:
    while lucene.state /= CLOSED \/ lucene.buffer /= <<>> do
        await lucene.buffer /= <<>>;
        lucene := [lucene EXCEPT
            !.document = ApplyBufferedOperations(lucene.buffer, @),
            !.buffer   = <<>>
            ];
    end while;
end process;


process ConsumerProcess = "Consumer"
variables
begin
  ConsumerLoop:
  while replication_requests /= {} do
    with replication_request \in replication_requests do
        replication_requests := replication_requests \ {replication_request};
        lucene := [lucene EXCEPT !.buffer = Append(@, replication_request)];
    end with;
  end while;
  
  lucene := [lucene EXCEPT !.state = CLOSED];
end process

end algorithm

*)
\* BEGIN TRANSLATION
VARIABLES request_count, replication_requests, expected_doc, 
          maxUnsafeAutoIdTimestamp, pc, lucene

vars == << request_count, replication_requests, expected_doc, 
           maxUnsafeAutoIdTimestamp, pc, lucene >>

ProcSet == {"ReplicaLucene"} \cup {"Consumer"}

Init == (* Global variables *)
        /\ request_count \in 1..4
        /\ replication_requests \in RequestSet(request_count)
        /\ expected_doc = FinalDoc(replication_requests)
        /\ maxUnsafeAutoIdTimestamp \in {0, DocAutoIdTimestamp - 1, DocAutoIdTimestamp, DocAutoIdTimestamp + 1}
        (* Process LuceneProcess *)
        /\ lucene = [ document |-> NULL
                    , buffer   |-> <<>>
                    , state    |-> OPEN
                    ]
        /\ pc = [self \in ProcSet |-> CASE self = "ReplicaLucene" -> "LuceneLoop"
                                        [] self = "Consumer" -> "ConsumerLoop"]

LuceneLoop == /\ pc["ReplicaLucene"] = "LuceneLoop"
              /\ IF lucene.state /= CLOSED \/ lucene.buffer /= <<>>
                    THEN /\ lucene.buffer /= <<>>
                         /\ lucene' =       [lucene EXCEPT
                                      !.document = ApplyBufferedOperations(lucene.buffer, @),
                                      !.buffer   = <<>>
                                      ]
                         /\ pc' = [pc EXCEPT !["ReplicaLucene"] = "LuceneLoop"]
                    ELSE /\ pc' = [pc EXCEPT !["ReplicaLucene"] = "Done"]
                         /\ UNCHANGED lucene
              /\ UNCHANGED << request_count, replication_requests, 
                              expected_doc, maxUnsafeAutoIdTimestamp >>

LuceneProcess == LuceneLoop

ConsumerLoop == /\ pc["Consumer"] = "ConsumerLoop"
                /\ IF replication_requests /= {}
                      THEN /\ \E replication_request \in replication_requests:
                                /\ replication_requests' = replication_requests \ {replication_request}
                                /\ lucene' = [lucene EXCEPT !.buffer = Append(@, replication_request)]
                           /\ pc' = [pc EXCEPT !["Consumer"] = "ConsumerLoop"]
                      ELSE /\ lucene' = [lucene EXCEPT !.state = CLOSED]
                           /\ pc' = [pc EXCEPT !["Consumer"] = "Done"]
                           /\ UNCHANGED replication_requests
                /\ UNCHANGED << request_count, expected_doc, 
                                maxUnsafeAutoIdTimestamp >>

ConsumerProcess == ConsumerLoop

Next == LuceneProcess \/ ConsumerProcess
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Terminated == \A self \in ProcSet: pc[self] = "Done"

Invariant == /\ Cardinality(replication_requests) <= 4
             /\ \/ expected_doc /= NULL
                \/ expected_doc  = NULL
             \* /\ Terminated => doc = expected_doc

=============================================================================
\* Modification History
\* Last modified Wed Mar 21 14:46:11 GMT 2018 by davidturner
\* Created Wed Mar 21 12:14:28 GMT 2018 by davidturner
