---- MODULE database ----

EXTENDS TLC, Integers

CONSTANTS NULL, Data, Clients

(*--algorithm database

variables
  db_value \in Data;

process client \in Clients
variables
  result  = NULL;
begin
  Client:
    either \* read
      result := db_value;
      assert result = db_value;
    or \* write
      with d \in Data do
        db_value := d;
      end with;
    end either;
    goto Client;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "3b48cb50" /\ chksum(tla) = "6457fc1a")
VARIABLES db_value, pc, result

vars == << db_value, pc, result >>

ProcSet == (Clients)

Init == (* Global variables *)
        /\ db_value \in Data
        (* Process client *)
        /\ result = [self \in Clients |-> NULL]
        /\ pc = [self \in ProcSet |-> "Client"]

Client(self) == /\ pc[self] = "Client"
                /\ \/ /\ result' = [result EXCEPT ![self] = db_value]
                      /\ Assert(result'[self] = db_value, 
                                "Failure of assertion at line 19, column 7.")
                      /\ UNCHANGED db_value
                   \/ /\ \E d \in Data:
                           db_value' = d
                      /\ UNCHANGED result
                /\ pc' = [pc EXCEPT ![self] = "Client"]

client(self) == Client(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Clients: client(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=========================
