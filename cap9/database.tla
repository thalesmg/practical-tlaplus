---- MODULE database ----

EXTENDS TLC, Integers

CONSTANTS NULL, Data, Clients

(*--algorithm database

variables
  query = [c \in Clients |-> NULL],
  db_value \in Data;

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
          assert result = db_value;
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
\* BEGIN TRANSLATION (chksum(pcal) = "134b3074" /\ chksum(tla) = "a13a1b56")
VARIABLES query, db_value, pc

(* define statement *)
Exists(val) == val /= NULL
RequestingClients == {c \in Clients : Exists(query[c]) /\ query[c].type = "request"}

VARIABLE result

vars == << query, db_value, pc, result >>

ProcSet == {"Database"} \cup (Clients)

Init == (* Global variables *)
        /\ query = [c \in Clients |-> NULL]
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
                                                   "Failure of assertion at line 36, column 9.")
                              /\ UNCHANGED db_value
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
                 /\ UNCHANGED << db_value, result >>

Confirm(self) == /\ pc[self] = "Confirm"
                 /\ query[self].type = "response"
                 /\ result' = [result EXCEPT ![self] = query[self].result]
                 /\ Assert(result'[self] = db_value, 
                           "Failure of assertion at line 54, column 11.")
                 /\ pc' = [pc EXCEPT ![self] = "Request"]
                 /\ UNCHANGED << query, db_value >>

Wait(self) == /\ pc[self] = "Wait"
              /\ query[self].type = "response"
              /\ pc' = [pc EXCEPT ![self] = "Request"]
              /\ UNCHANGED << query, db_value, result >>

client(self) == Request(self) \/ Confirm(self) \/ Wait(self)

Next == database
           \/ (\E self \in Clients: client(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=========================
