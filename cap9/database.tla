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
  query[self] := [type |-> "request", data |-> data];
end macro;

macro wait_for_response() begin
  await query[self].type = "response";
end macro;

process database = "Database"
begin
  Database:
    with c \in RequestingClients,
      q = query[c] do
      db_value := q.data;
      query[c] := [type |-> "response"];
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
        result := db_value;
        assert result = db_value;
      or \* write
        with d \in Data do
          request(d);
        end with;
        Wait:
          wait_for_response();
      end either;
    end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "dfcce7b2" /\ chksum(tla) = "764f0e3d")
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
                   /\ db_value' = q.data
                   /\ query' = [query EXCEPT ![c] = [type |-> "response"]]
            /\ pc' = [pc EXCEPT !["Database"] = "Database"]
            /\ UNCHANGED result

database == Database

Request(self) == /\ pc[self] = "Request"
                 /\ \/ /\ result' = [result EXCEPT ![self] = db_value]
                       /\ Assert(result'[self] = db_value, 
                                 "Failure of assertion at line 45, column 9.")
                       /\ pc' = [pc EXCEPT ![self] = "Request"]
                       /\ query' = query
                    \/ /\ \E d \in Data:
                            query' = [query EXCEPT ![self] = [type |-> "request", data |-> d]]
                       /\ pc' = [pc EXCEPT ![self] = "Wait"]
                       /\ UNCHANGED result
                 /\ UNCHANGED db_value

Wait(self) == /\ pc[self] = "Wait"
              /\ query[self].type = "response"
              /\ pc' = [pc EXCEPT ![self] = "Request"]
              /\ UNCHANGED << query, db_value, result >>

client(self) == Request(self) \/ Wait(self)

Next == database
           \/ (\E self \in Clients: client(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=========================
