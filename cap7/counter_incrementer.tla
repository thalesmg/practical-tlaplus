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
  GetAndIncrement:
    local := counter;
  \* Increment:
    counter := local + 1;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "c15dfb6" /\ chksum(tla) = "a587a8b9")
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
        /\ pc = [self \in ProcSet |-> "GetAndIncrement"]

GetAndIncrement(self) == /\ pc[self] = "GetAndIncrement"
                         /\ local' = [local EXCEPT ![self] = counter]
                         /\ counter' = local'[self] + 1
                         /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ goal' = goal

incrementer(self) == GetAndIncrement(self)

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
