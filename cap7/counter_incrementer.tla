---- MODULE counter_incrementer ----

EXTENDS TLC, Integers

(*--algorithm counter_incrementer
variables
  goal = 3,
  counter = 0;

define
  Success == <>[](counter = goal)
end define;

fair process incrementer \in 1..3
variable local = 0
begin
  Get:
    local := counter;
  Increment:
    counter := local + 1;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "c9c84a96" /\ chksum(tla) = "258d42fc")
VARIABLES goal, counter, pc

(* define statement *)
Success == <>[](counter = goal)

VARIABLE local

vars == << goal, counter, pc, local >>

ProcSet == (1..3)

Init == (* Global variables *)
        /\ goal = 3
        /\ counter = 0
        (* Process incrementer *)
        /\ local = [self \in 1..3 |-> 0]
        /\ pc = [self \in ProcSet |-> "Get"]

Get(self) == /\ pc[self] = "Get"
             /\ local' = [local EXCEPT ![self] = counter]
             /\ pc' = [pc EXCEPT ![self] = "Increment"]
             /\ UNCHANGED << goal, counter >>

Increment(self) == /\ pc[self] = "Increment"
                   /\ counter' = local[self] + 1
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << goal, local >>

incrementer(self) == Get(self) \/ Increment(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..3: incrementer(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..3 : WF_vars(incrementer(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====================================
