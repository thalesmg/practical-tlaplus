--------- MODULE wire2 ---------------
EXTENDS Integers

(*--algorithm wire2
variables
  people = {"maria", "jao"},
  acc = [p \in people |-> 5];

define
  NoOverdrafts == \A p \in people: acc[p] >= 0
  EventuallyConsistent == <>[](acc["maria"] + acc["jao"] = 10)
end define;

process Wire \in 1..2
  variables
    sender = "maria",
    receiver = "jao",
    amount \in 1..acc[sender];
  begin
    CheckAndWithdraw:
      if amount <= acc[sender] then
          acc[sender] := acc[sender] - amount;
        Deposit:
          acc[receiver] := acc[receiver] + amount;
      end if;
end process;

end algorithm;*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-c457829b30f9cc9cb2a9bf7653e268b0
VARIABLES people, acc, pc

(* define statement *)
NoOverdrafts == \A p \in people: acc[p] >= 0
EventuallyConsistent == <>[](acc["maria"] + acc["jao"] = 10)

VARIABLES sender, receiver, amount

vars == << people, acc, pc, sender, receiver, amount >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ people = {"maria", "jao"}
        /\ acc = [p \in people |-> 5]
        (* Process Wire *)
        /\ sender = [self \in 1..2 |-> "maria"]
        /\ receiver = [self \in 1..2 |-> "jao"]
        /\ amount \in [1..2 -> 1..acc[sender[CHOOSE self \in  1..2 : TRUE]]]
        /\ pc = [self \in ProcSet |-> "CheckAndWithdraw"]

CheckAndWithdraw(self) == /\ pc[self] = "CheckAndWithdraw"
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

Wire(self) == CheckAndWithdraw(self) \/ Deposit(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..2: Wire(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-630c93d46395cb28946004ba5a8aaad8
=============================================
