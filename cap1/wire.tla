-------------------------------- MODULE wire --------------------------------

EXTENDS Integers

(*--algorithm wire
variables
    people = {"alice", "bob"},
    acc = [p \in people |-> 5];

define
    NoOverdrafts == \A p \in people: acc[p] >= 0
    EventuallyConsistent == <>[](acc["alice"] + acc["bob"] = 10)
end define;

process Wire \in 1..2
    variables
        sender = "alice",
        receiver = "bob",
        amount \in 1..acc[sender];
    begin
        CheckFunds:
            if amount <= acc[sender] then
                    acc[sender] := acc[sender] - amount;
                Deposit:
                    acc[receiver] := acc[receiver] + amount;
            end if;
end process;            
           
end algorithm;*)
\* BEGIN TRANSLATION PCal-abed4595ab5f660e99e6373a12aec987
VARIABLES people, acc, pc

(* define statement *)
NoOverdrafts == \A p \in people: acc[p] >= 0
EventuallyConsistent == <>[](acc["alice"] + acc["bob"] = 10)

VARIABLES sender, receiver, amount

vars == << people, acc, pc, sender, receiver, amount >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ people = {"alice", "bob"}
        /\ acc = [p \in people |-> 5]
        (* Process Wire *)
        /\ sender = [self \in 1..2 |-> "alice"]
        /\ receiver = [self \in 1..2 |-> "bob"]
        /\ amount \in [1..2 -> 1..acc[sender[CHOOSE self \in  1..2 : TRUE]]]
        /\ pc = [self \in ProcSet |-> "CheckFunds"]

CheckFunds(self) == /\ pc[self] = "CheckFunds"
                    /\ IF amount[self] <= acc[sender[self]]
                          THEN /\ acc' = [acc EXCEPT ![sender[self]] = acc[sender[self]] - amount[self]]
                               /\ pc' = [pc EXCEPT ![self] = "Deposit"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ acc' = acc
                    /\ UNCHANGED << people, sender, receiver, amount >>

Deposit(self) == /\ pc[self] = "Deposit"
                 /\ acc' = [acc EXCEPT ![receiver[self]] = acc[receiver[self]] + amount[self]]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << people, sender, receiver, amount >>

Wire(self) == CheckFunds(self) \/ Deposit(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..2: Wire(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION TLA-a22177ae73e0dc9f1f587ff0d2ef90ea

=============================================================================
\* Modification History
\* Last modified Thu Feb 11 18:31:14 BRT 2021 by thales
\* Created Sun Dec 30 20:28:35 BRST 2018 by thales
