---- MODULE main ----

EXTENDS TLC, Sequences, Integers, FiniteSets

PT == INSTANCE PT

CONSTANTS Workers, Reducer, NULL

MaxValue == 2
NumItems == 4
PossibleInputs == PT!TupleOf(0..MaxValue, NumItems)

SumSeq(seq) == PT!ReduceSeq(LAMBDA x, y: x + y, seq, 0)

FairWorkers == CHOOSE ws \in SUBSET Workers : Cardinality(ws) = 1
UnfairWorkers == Workers \ FairWorkers

(*--algorithm mapreduce

variables
  input \in PossibleInputs,
  queue = [w \in Workers |-> <<>>],
  result = [w \in Workers |-> NULL];

macro reduce() begin
  with w \in {w \in Workers: ~consumed[w] /\ result[w] /= NULL} do
    final := final + result[w];
    consumed[w] := TRUE;
  end with;
end macro;

procedure work()
  variables
    total = 0;
  begin
    WaitForQueue:
      await queue[self] /= <<>>;
    Process:
      while queue[self] /= <<>> do
        total := total + Head(queue[self]);
        queue[self] := Tail(queue[self]);
      end while;
    WriteResult:
      result[self] := total;
      goto WaitForQueue;
end procedure;

fair process reducer = Reducer
variables
  final = 0,
  assignments = [w \in Workers |-> <<>>],
  consumed = [w \in Workers |-> FALSE];
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
    while \E w \in Workers : ~consumed[w] do
      either
        reduce();
      or \* reassign
        with from_worker \in {w \in UnfairWorkers : ~consumed[w] /\ result[w] = NULL},
             to_worker \in FairWorkers do
          \* mark failed as consumed to avoid reading it again
          \* unmark the fair worker to wait on it again
          \*
          \* must use `||` because assigning twice to the same
          \* variable inside a label is forbidden
          consumed[from_worker] := TRUE || consumed[to_worker] := FALSE;
          assignments[to_worker] :=
            assignments[to_worker] \o assignments[from_worker];
          queue[to_worker] := queue[to_worker] \o assignments[from_worker];
        end with;
      end either;
    end while;
  Finish:
    assert final = SumSeq(input);
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
\* BEGIN TRANSLATION (chksum(pcal) = "a7940d31" /\ chksum(tla) = "bbab062f")
VARIABLES input, queue, result, pc, stack, total, final, assignments,
          consumed

vars == << input, queue, result, pc, stack, total, final, assignments,
           consumed >>

ProcSet == {Reducer} \cup (Workers)

Init == (* Global variables *)
        /\ input \in PossibleInputs
        /\ queue = [w \in Workers |-> <<>>]
        /\ result = [w \in Workers |-> NULL]
        (* Procedure work *)
        /\ total = [ self \in ProcSet |-> 0]
        (* Process reducer *)
        /\ final = 0
        /\ assignments = [w \in Workers |-> <<>>]
        /\ consumed = [w \in Workers |-> FALSE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = Reducer -> "Schedule"
                                        [] self \in Workers -> "Work"]

WaitForQueue(self) == /\ pc[self] = "WaitForQueue"
                      /\ queue[self] /= <<>>
                      /\ pc' = [pc EXCEPT ![self] = "Process"]
                      /\ UNCHANGED << input, queue, result, stack, total,
                                      final, assignments, consumed >>

Process(self) == /\ pc[self] = "Process"
                 /\ IF queue[self] /= <<>>
                       THEN /\ total' = [total EXCEPT ![self] = total[self] + Head(queue[self])]
                            /\ queue' = [queue EXCEPT ![self] = Tail(queue[self])]
                            /\ pc' = [pc EXCEPT ![self] = "Process"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "WriteResult"]
                            /\ UNCHANGED << queue, total >>
                 /\ UNCHANGED << input, result, stack, final, assignments,
                                 consumed >>

WriteResult(self) == /\ pc[self] = "WriteResult"
                     /\ result' = [result EXCEPT ![self] = total[self]]
                     /\ pc' = [pc EXCEPT ![self] = "WaitForQueue"]
                     /\ UNCHANGED << input, queue, stack, total, final,
                                     assignments, consumed >>

work(self) == WaitForQueue(self) \/ Process(self) \/ WriteResult(self)

Schedule == /\ pc[Reducer] = "Schedule"
            /\ LET worker_order == PT!OrderSet(Workers) IN
                 /\ queue' =          [ w \in Workers |->
                               LET offset == PT!Index(worker_order, w) - 1
                               IN PT!SelectSeqByIndex(input, LAMBDA i: i % Len(worker_order) = offset)
                             ]
                 /\ assignments' = queue'
            /\ pc' = [pc EXCEPT ![Reducer] = "Reduce"]
            /\ UNCHANGED << input, result, stack, total, final, consumed >>

Reduce == /\ pc[Reducer] = "Reduce"
          /\ IF \E w \in Workers : ~consumed[w]
                THEN /\ \/ /\ \E w \in {w \in Workers: ~consumed[w] /\ result[w] /= NULL}:
                                /\ final' = final + result[w]
                                /\ consumed' = [consumed EXCEPT ![w] = TRUE]
                           /\ UNCHANGED <<queue, assignments>>
                        \/ /\ \E from_worker \in {w \in UnfairWorkers : ~consumed[w] /\ result[w] = NULL}:
                                \E to_worker \in FairWorkers:
                                  /\ consumed' = [consumed EXCEPT ![from_worker] = TRUE,
                                                                  ![to_worker] = FALSE]
                                  /\ assignments' = [assignments EXCEPT ![to_worker] = assignments[to_worker] \o assignments[from_worker]]
                                  /\ queue' = [queue EXCEPT ![to_worker] = queue[to_worker] \o assignments'[from_worker]]
                           /\ final' = final
                     /\ pc' = [pc EXCEPT ![Reducer] = "Reduce"]
                ELSE /\ pc' = [pc EXCEPT ![Reducer] = "Finish"]
                     /\ UNCHANGED << queue, final, assignments, consumed >>
          /\ UNCHANGED << input, result, stack, total >>

Finish == /\ pc[Reducer] = "Finish"
          /\ Assert(final = SumSeq(input),
                    "Failure of assertion at line 82, column 5.")
          /\ pc' = [pc EXCEPT ![Reducer] = "Done"]
          /\ UNCHANGED << input, queue, result, stack, total, final,
                          assignments, consumed >>

reducer == Schedule \/ Reduce \/ Finish

Work(self) == /\ pc[self] = "Work"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "work",
                                                       pc        |->  "Done",
                                                       total     |->  total[self] ] >>
                                                   \o stack[self]]
              /\ total' = [total EXCEPT ![self] = 0]
              /\ pc' = [pc EXCEPT ![self] = "WaitForQueue"]
              /\ UNCHANGED << input, queue, result, final, assignments,
                              consumed >>

worker(self) == Work(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == reducer
           \/ (\E self \in ProcSet: work(self))
           \/ (\E self \in Workers: worker(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(reducer)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Liveness ==
  <>[](final = SumSeq(input))

=====================
