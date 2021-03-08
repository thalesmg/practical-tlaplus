---- MODULE database ----

EXTENDS TLC, Integers

CONSTANTS NULL, Data, Clients

(*--algorithm database

variables
  query = [c \in Clients |-> NULL],
  ghost_db_history = [c \in Clients |-> NULL];

define
  Exists(val) == val /= NULL
  RequestingClients == {c \in Clients : Exists(query[c]) /\ query[c].type = "request"}
end define;

macro request(data) begin
  query[self] := [type |-> "request"] @@ data;
end macro;

macro wait_for_response() begin
  await query[self].type = "response";
end macro;

process database = "Database"
variables
  db_value \in Data;
begin
  Database:
    with c \in RequestingClients,
      q = query[c] do
      if q.request = "write" then
        db_value := q.data;
      elsif q.request = "read" then
        skip;
      else
        assert FALSE;
      end if;
      ghost_db_history[c] := db_value;
      query[c] := [type |-> "response", result |-> db_value];
    end with;
    goto Database;
end process;

process client \in Clients
variables
  result  = NULL;
begin
  Request:
    while TRUE do
      either \* read
        request([request |-> "read"]);
        Confirm:
          wait_for_response();
          result := query[self].result;
          assert result = ghost_db_history[self];
      or \* write
        with d \in Data do
          request([request |-> "write", data |-> d]);
        end with;
        Wait:
          wait_for_response();
      end either;
    end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "8caf3f93" /\ chksum(tla) = "e2b48012")
VARIABLES query, ghost_db_history, pc

(* define statement *)
Exists(val) == val /= NULL
RequestingClients == {c \in Clients : Exists(query[c]) /\ query[c].type = "request"}

VARIABLES db_value, result

vars == << query, ghost_db_history, pc, db_value, result >>

ProcSet == {"Database"} \cup (Clients)

Init == (* Global variables *)
        /\ query = [c \in Clients |-> NULL]
        /\ ghost_db_history = [c \in Clients |-> NULL]
        (* Process database *)
        /\ db_value \in Data
        (* Process client *)
        /\ result = [self \in Clients |-> NULL]
        /\ pc = [self \in ProcSet |-> CASE self = "Database" -> "Database"
                                        [] self \in Clients -> "Request"]

Database == /\ pc["Database"] = "Database"
            /\ \E c \in RequestingClients:
                 LET q == query[c] IN
                   /\ IF q.request = "write"
                         THEN /\ db_value' = q.data
                         ELSE /\ IF q.request = "read"
                                    THEN /\ TRUE
                                    ELSE /\ Assert(FALSE, 
                                                   "Failure of assertion at line 38, column 9.")
                              /\ UNCHANGED db_value
                   /\ ghost_db_history' = [ghost_db_history EXCEPT ![c] = db_value']
                   /\ query' = [query EXCEPT ![c] = [type |-> "response", result |-> db_value']]
            /\ pc' = [pc EXCEPT !["Database"] = "Database"]
            /\ UNCHANGED result

database == Database

Request(self) == /\ pc[self] = "Request"
                 /\ \/ /\ query' = [query EXCEPT ![self] = [type |-> "request"] @@ ([request |-> "read"])]
                       /\ pc' = [pc EXCEPT ![self] = "Confirm"]
                    \/ /\ \E d \in Data:
                            query' = [query EXCEPT ![self] = [type |-> "request"] @@ ([request |-> "write", data |-> d])]
                       /\ pc' = [pc EXCEPT ![self] = "Wait"]
                 /\ UNCHANGED << ghost_db_history, db_value, result >>

Confirm(self) == /\ pc[self] = "Confirm"
                 /\ query[self].type = "response"
                 /\ result' = [result EXCEPT ![self] = query[self].result]
                 /\ Assert(result'[self] = ghost_db_history[self], 
                           "Failure of assertion at line 57, column 11.")
                 /\ pc' = [pc EXCEPT ![self] = "Request"]
                 /\ UNCHANGED << query, ghost_db_history, db_value >>

Wait(self) == /\ pc[self] = "Wait"
              /\ query[self].type = "response"
              /\ pc' = [pc EXCEPT ![self] = "Request"]
              /\ UNCHANGED << query, ghost_db_history, db_value, result >>

client(self) == Request(self) \/ Confirm(self) \/ Wait(self)

Next == database
           \/ (\E self \in Clients: client(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=========================
