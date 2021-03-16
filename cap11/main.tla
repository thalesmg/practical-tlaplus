---- MODULE main ----

EXTENDS TLC, Sequences, Integers, FiniteSets

PT == INSTANCE PT

CONSTANTS Workers, Reducer, NULL
CONSTANTS ItemRange, ItemCount

ASSUME ItemRange \subseteq Nat
ASSUME ItemCount \in Nat

PossibleInputs == PT!TupleOf(ItemRange, ItemCount)

SumSeq(seq) == PT!ReduceSeq(LAMBDA x, y: x + y, seq, 0)

FairWorkers == CHOOSE ws \in SUBSET Workers : Cardinality(ws) = 1
UnfairWorkers == Workers \ FairWorkers

(*--algorithm mapreduce

variables
  input \in PossibleInputs,
  queue = [w \in Workers |-> <<>>],
  \* for reducer usage only
  status = [w \in Workers |-> "active"],
  result = [w \in Workers |-> [total |-> NULL, count |-> NULL]];

define
  ActiveWorkers == {w \in Workers : status[w] = "active"}
  HealthyWorkers == {w \in Workers : status[w] /= "broken"}
  TypeInvariant ==
    /\ status \in [Workers -> {"active", "inactive", "broken"}]
    /\ \A w \in Workers:
         /\ Len(queue[w]) <= ItemCount

         /\ \A item \in 1..Len(queue[w]):
              queue[w][item] \in ItemRange

         /\ \/ result[w].total = NULL
            \/ result[w].total <= SumSeq(input)

         /\ \/ result[w].count = NULL
            \/ result[w].count <= ItemCount

end define;

macro reduce() begin
  with w \in {w \in ActiveWorkers : result[w].count = Len(assignments[w])} do
    final[w] := result[w].total;
    status[w] := "inactive";
  end with;
end macro;

procedure work()
  variables
    total = 0,
    count = 0;
  begin
    WaitForQueue:
      await queue[self] /= <<>>;
    Process:
      while queue[self] /= <<>> do
        total := total + Head(queue[self]);
        queue[self] := Tail(queue[self]);
        count := count + 1;
      end while;
    WriteResult:
      result[self] := [total |-> total, count |-> count];
      goto WaitForQueue;
end procedure;

fair process reducer = Reducer
variables
  assignments = [w \in Workers |-> <<>>],
  final = [w \in Workers |-> 0];
begin
  Schedule:
    with worker_order = PT!OrderSet(Workers) do
      queue := [ w \in Workers |->
        LET offset == PT!Index(worker_order, w) - 1
        IN PT!SelectSeqByIndex(input, LAMBDA i: i % Len(worker_order) = offset)
      ];
      assignments := queue;
    end with;
  Reduce:
    while ActiveWorkers /= {} do
      either
        reduce();
      or \* reassign
        with from_worker \in ActiveWorkers \ FairWorkers,
             to_worker \in HealthyWorkers \ {from_worker} do
          \* mark failed as consumed to avoid reading it again
          \* unmark the fair worker to wait on it again
          \*
          \* must use `||` because assigning twice to the same
          \* variable inside a label is forbidden
          status[from_worker] := "broken" || status[to_worker] := "active";
          assignments[to_worker] :=
            assignments[to_worker] \o assignments[from_worker];
          queue[to_worker] := queue[to_worker] \o assignments[from_worker];
          final[to_worker] := 0;
        end with;
      end either;
    end while;
  Finish:
    assert SumSeq(final) = SumSeq(input);
end process;

fair process fair_worker \in FairWorkers
begin
  FairWorker:
    call work();
end process;

process unfair_worker \in UnfairWorkers
begin
  UnfairWorker:
    call work();
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "ce7afc45" /\ chksum(tla) = "98f0772")
VARIABLES input, queue, status, result, pc, stack

(* define statement *)
ActiveWorkers == {w \in Workers : status[w] = "active"}
HealthyWorkers == {w \in Workers : status[w] /= "broken"}
TypeInvariant ==
  /\ status \in [Workers -> {"active", "inactive", "broken"}]
  /\ \A w \in Workers:
       /\ Len(queue[w]) <= ItemCount

       /\ \A item \in 1..Len(queue[w]):
            queue[w][item] \in ItemRange

       /\ \/ result[w].total = NULL
          \/ result[w].total <= SumSeq(input)

       /\ \/ result[w].count = NULL
          \/ result[w].count <= ItemCount

VARIABLES total, count, assignments, final

vars == << input, queue, status, result, pc, stack, total, count, assignments, 
           final >>

ProcSet == {Reducer} \cup (FairWorkers) \cup (UnfairWorkers)

Init == (* Global variables *)
        /\ input \in PossibleInputs
        /\ queue = [w \in Workers |-> <<>>]
        /\ status = [w \in Workers |-> "active"]
        /\ result = [w \in Workers |-> [total |-> NULL, count |-> NULL]]
        (* Procedure work *)
        /\ total = [ self \in ProcSet |-> 0]
        /\ count = [ self \in ProcSet |-> 0]
        (* Process reducer *)
        /\ assignments = [w \in Workers |-> <<>>]
        /\ final = [w \in Workers |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = Reducer -> "Schedule"
                                        [] self \in FairWorkers -> "FairWorker"
                                        [] self \in UnfairWorkers -> "UnfairWorker"]

WaitForQueue(self) == /\ pc[self] = "WaitForQueue"
                      /\ queue[self] /= <<>>
                      /\ pc' = [pc EXCEPT ![self] = "Process"]
                      /\ UNCHANGED << input, queue, status, result, stack, 
                                      total, count, assignments, final >>

Process(self) == /\ pc[self] = "Process"
                 /\ IF queue[self] /= <<>>
                       THEN /\ total' = [total EXCEPT ![self] = total[self] + Head(queue[self])]
                            /\ queue' = [queue EXCEPT ![self] = Tail(queue[self])]
                            /\ count' = [count EXCEPT ![self] = count[self] + 1]
                            /\ pc' = [pc EXCEPT ![self] = "Process"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "WriteResult"]
                            /\ UNCHANGED << queue, total, count >>
                 /\ UNCHANGED << input, status, result, stack, assignments, 
                                 final >>

WriteResult(self) == /\ pc[self] = "WriteResult"
                     /\ result' = [result EXCEPT ![self] = [total |-> total[self], count |-> count[self]]]
                     /\ pc' = [pc EXCEPT ![self] = "WaitForQueue"]
                     /\ UNCHANGED << input, queue, status, stack, total, count, 
                                     assignments, final >>

work(self) == WaitForQueue(self) \/ Process(self) \/ WriteResult(self)

Schedule == /\ pc[Reducer] = "Schedule"
            /\ LET worker_order == PT!OrderSet(Workers) IN
                 /\ queue' =          [ w \in Workers |->
                               LET offset == PT!Index(worker_order, w) - 1
                               IN PT!SelectSeqByIndex(input, LAMBDA i: i % Len(worker_order) = offset)
                             ]
                 /\ assignments' = queue'
            /\ pc' = [pc EXCEPT ![Reducer] = "Reduce"]
            /\ UNCHANGED << input, status, result, stack, total, count, final >>

Reduce == /\ pc[Reducer] = "Reduce"
          /\ IF ActiveWorkers /= {}
                THEN /\ \/ /\ \E w \in {w \in ActiveWorkers : result[w].count = Len(assignments[w])}:
                                /\ final' = [final EXCEPT ![w] = result[w].total]
                                /\ status' = [status EXCEPT ![w] = "inactive"]
                           /\ UNCHANGED <<queue, assignments>>
                        \/ /\ \E from_worker \in ActiveWorkers \ FairWorkers:
                                \E to_worker \in HealthyWorkers \ {from_worker}:
                                  /\ status' = [status EXCEPT ![from_worker] = "broken",
                                                              ![to_worker] = "active"]
                                  /\ assignments' = [assignments EXCEPT ![to_worker] = assignments[to_worker] \o assignments[from_worker]]
                                  /\ queue' = [queue EXCEPT ![to_worker] = queue[to_worker] \o assignments'[from_worker]]
                                  /\ final' = [final EXCEPT ![to_worker] = 0]
                     /\ pc' = [pc EXCEPT ![Reducer] = "Reduce"]
                ELSE /\ pc' = [pc EXCEPT ![Reducer] = "Finish"]
                     /\ UNCHANGED << queue, status, assignments, final >>
          /\ UNCHANGED << input, result, stack, total, count >>

Finish == /\ pc[Reducer] = "Finish"
          /\ Assert(SumSeq(final) = SumSeq(input), 
                    "Failure of assertion at line 107, column 5.")
          /\ pc' = [pc EXCEPT ![Reducer] = "Done"]
          /\ UNCHANGED << input, queue, status, result, stack, total, count, 
                          assignments, final >>

reducer == Schedule \/ Reduce \/ Finish

FairWorker(self) == /\ pc[self] = "FairWorker"
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "work",
                                                             pc        |->  "Done",
                                                             total     |->  total[self],
                                                             count     |->  count[self] ] >>
                                                         \o stack[self]]
                    /\ total' = [total EXCEPT ![self] = 0]
                    /\ count' = [count EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "WaitForQueue"]
                    /\ UNCHANGED << input, queue, status, result, assignments, 
                                    final >>

fair_worker(self) == FairWorker(self)

UnfairWorker(self) == /\ pc[self] = "UnfairWorker"
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "work",
                                                               pc        |->  "Done",
                                                               total     |->  total[self],
                                                               count     |->  count[self] ] >>
                                                           \o stack[self]]
                      /\ total' = [total EXCEPT ![self] = 0]
                      /\ count' = [count EXCEPT ![self] = 0]
                      /\ pc' = [pc EXCEPT ![self] = "WaitForQueue"]
                      /\ UNCHANGED << input, queue, status, result, 
                                      assignments, final >>

unfair_worker(self) == UnfairWorker(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == reducer
           \/ (\E self \in ProcSet: work(self))
           \/ (\E self \in FairWorkers: fair_worker(self))
           \/ (\E self \in UnfairWorkers: unfair_worker(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(reducer)
        /\ \A self \in FairWorkers : WF_vars(fair_worker(self)) /\ WF_vars(work(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Liveness ==
  <>[](SumSeq(final) = SumSeq(input))

=====================
