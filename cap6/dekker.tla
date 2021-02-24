---- MODULE dekker ----

EXTENDS TLC, Integers, Sequences
CONSTANT Threads

\* Threads == 1..2

(*--algorithm dekker
variables
  flag = [t \in Threads |-> FALSE],
  next_thread \in Threads;

define
  Max(xs) == CHOOSE x \in xs: \A y \in xs \ {x}: x >= y
  NextThread(current) == IF current = Max(Threads) THEN 1 ELSE current + 1
end define;

procedure thread()
begin
  P1: flag[self] := TRUE;
  P2:
    while next_thread /= self \/ \E t \in Threads \ {self} : flag[t] do
      P2_1:
        if next_thread /= self then
          P2_1_1: flag[self] := FALSE;
          P2_1_2: await next_thread = self;
          P2_1_3: flag[self] := TRUE;
        end if;
    end while;
  \* critical section
  CS: skip;
  P3: next_thread := NextThread(next_thread);
  P4: flag[self] := FALSE;
  P5: goto P1;
end procedure;

fair process fair_thread \in Threads
begin
  Fair:
    call thread();
end process;

\* process crashable_thread \in {2}
\* begin
\*   Crash:
\*     call thread();
\* end process;

end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "66b63d51" /\ chksum(tla) = "7c53e61b")
VARIABLES flag, next_thread, pc, stack

(* define statement *)
Max(xs) == CHOOSE x \in xs: \A y \in xs \ {x}: x >= y
NextThread(current) == IF current = Max(Threads) THEN 1 ELSE current + 1


vars == << flag, next_thread, pc, stack >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ flag = [t \in Threads |-> FALSE]
        /\ next_thread \in Threads
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Fair"]

P1(self) == /\ pc[self] = "P1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "P2"]
            /\ UNCHANGED << next_thread, stack >>

P2(self) == /\ pc[self] = "P2"
            /\ IF next_thread /= self \/ \E t \in Threads \ {self} : flag[t]
                  THEN /\ pc' = [pc EXCEPT ![self] = "P2_1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "CS"]
            /\ UNCHANGED << flag, next_thread, stack >>

P2_1(self) == /\ pc[self] = "P2_1"
              /\ IF next_thread /= self
                    THEN /\ pc' = [pc EXCEPT ![self] = "P2_1_1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "P2"]
              /\ UNCHANGED << flag, next_thread, stack >>

P2_1_1(self) == /\ pc[self] = "P2_1_1"
                /\ flag' = [flag EXCEPT ![self] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = "P2_1_2"]
                /\ UNCHANGED << next_thread, stack >>

P2_1_2(self) == /\ pc[self] = "P2_1_2"
                /\ next_thread = self
                /\ pc' = [pc EXCEPT ![self] = "P2_1_3"]
                /\ UNCHANGED << flag, next_thread, stack >>

P2_1_3(self) == /\ pc[self] = "P2_1_3"
                /\ flag' = [flag EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "P2"]
                /\ UNCHANGED << next_thread, stack >>

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "P3"]
            /\ UNCHANGED << flag, next_thread, stack >>

P3(self) == /\ pc[self] = "P3"
            /\ next_thread' = NextThread(next_thread)
            /\ pc' = [pc EXCEPT ![self] = "P4"]
            /\ UNCHANGED << flag, stack >>

P4(self) == /\ pc[self] = "P4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "P5"]
            /\ UNCHANGED << next_thread, stack >>

P5(self) == /\ pc[self] = "P5"
            /\ pc' = [pc EXCEPT ![self] = "P1"]
            /\ UNCHANGED << flag, next_thread, stack >>

thread(self) == P1(self) \/ P2(self) \/ P2_1(self) \/ P2_1_1(self)
                   \/ P2_1_2(self) \/ P2_1_3(self) \/ CS(self) \/ P3(self)
                   \/ P4(self) \/ P5(self)

Fair(self) == /\ pc[self] = "Fair"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "thread",
                                                       pc        |->  "Done" ] >>
                                                   \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "P1"]
              /\ UNCHANGED << flag, next_thread >>

fair_thread(self) == Fair(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: thread(self))
           \/ (\E self \in Threads: fair_thread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : WF_vars(fair_thread(self)) /\ WF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

ThereCanBeOnlyOne ==
  \A t1, t2 \in Threads:
    t1 /= t2 => ~( pc[t1] = "CS" /\ pc[t2] = "CS" )

Liveness ==
  \A t \in Threads:
    <>( pc[t] = "CS" )

===========================
