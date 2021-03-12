---- MODULE main ----

EXTENDS TLC, Sequences, Integers

PT == INSTANCE PT

CONSTANTS Workers, Reducer, NULL

MaxValue == 2
NumItems == 4
PossibleInputs == PT!TupleOf(0..MaxValue, NumItems)

SumSeq(seq) == PT!ReduceSeq(LAMBDA x, y: x + y, seq, 0)

(*--algorithm mapreduce

variables
  input \in PossibleInputs,
  queue = [w \in Workers |-> <<>>],
  result = [w \in Workers |-> NULL];

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
end procedure;

process reducer = Reducer
variables
  final = 0,
  consumed = [w \in Workers |-> FALSE];
begin
  Schedule:
    with worker_order = PT!OrderSet(Workers) do
      queue := [ w \in Workers |->
        LET offset == PT!Index(worker_order, w) - 1
        IN PT!SelectSeqByIndex(input, LAMBDA i: i % Len(worker_order) = offset)
      ];
    end with;
    skip;
  Reduce:
    while \E w \in Workers : ~consumed[w] do
      with w \in {w \in Workers: ~consumed[w] /\ result[w] /= NULL} do
        final := final + result[w];
        consumed[w] := TRUE;
      end with;
    end while;
  Finish:
    assert final = SumSeq(input);
end process;

process worker \in Workers
begin
  Work:
    call work();
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "2c4474ea" /\ chksum(tla) = "392445b2")
VARIABLES input, queue, result, pc, stack, total, final, consumed

vars == << input, queue, result, pc, stack, total, final, consumed >>

ProcSet == {Reducer} \cup (Workers)

Init == (* Global variables *)
        /\ input \in PossibleInputs
        /\ queue = [w \in Workers |-> <<>>]
        /\ result = [w \in Workers |-> NULL]
        (* Procedure work *)
        /\ total = [ self \in ProcSet |-> 0]
        (* Process reducer *)
        /\ final = 0
        /\ consumed = [w \in Workers |-> FALSE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = Reducer -> "Schedule"
                                        [] self \in Workers -> "Work"]

WaitForQueue(self) == /\ pc[self] = "WaitForQueue"
                      /\ queue[self] /= <<>>
                      /\ pc' = [pc EXCEPT ![self] = "Process"]
                      /\ UNCHANGED << input, queue, result, stack, total, 
                                      final, consumed >>

Process(self) == /\ pc[self] = "Process"
                 /\ IF queue[self] /= <<>>
                       THEN /\ total' = [total EXCEPT ![self] = total[self] + Head(queue[self])]
                            /\ queue' = [queue EXCEPT ![self] = Tail(queue[self])]
                            /\ pc' = [pc EXCEPT ![self] = "Process"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "WriteResult"]
                            /\ UNCHANGED << queue, total >>
                 /\ UNCHANGED << input, result, stack, final, consumed >>

WriteResult(self) == /\ pc[self] = "WriteResult"
                     /\ result' = [result EXCEPT ![self] = total[self]]
                     /\ pc' = [pc EXCEPT ![self] = "Error"]
                     /\ UNCHANGED << input, queue, stack, total, final, 
                                     consumed >>

work(self) == WaitForQueue(self) \/ Process(self) \/ WriteResult(self)

Schedule == /\ pc[Reducer] = "Schedule"
            /\ LET worker_order == PT!OrderSet(Workers) IN
                 queue' =          [ w \in Workers |->
                            LET offset == PT!Index(worker_order, w) - 1
                            IN PT!SelectSeqByIndex(input, LAMBDA i: i % Len(worker_order) = offset)
                          ]
            /\ TRUE
            /\ pc' = [pc EXCEPT ![Reducer] = "Reduce"]
            /\ UNCHANGED << input, result, stack, total, final, consumed >>

Reduce == /\ pc[Reducer] = "Reduce"
          /\ IF \E w \in Workers : ~consumed[w]
                THEN /\ \E w \in {w \in Workers: ~consumed[w] /\ result[w] /= NULL}:
                          /\ final' = final + result[w]
                          /\ consumed' = [consumed EXCEPT ![w] = TRUE]
                     /\ pc' = [pc EXCEPT ![Reducer] = "Reduce"]
                ELSE /\ pc' = [pc EXCEPT ![Reducer] = "Finish"]
                     /\ UNCHANGED << final, consumed >>
          /\ UNCHANGED << input, queue, result, stack, total >>

Finish == /\ pc[Reducer] = "Finish"
          /\ Assert(final = SumSeq(input), 
                    "Failure of assertion at line 58, column 5.")
          /\ pc' = [pc EXCEPT ![Reducer] = "Done"]
          /\ UNCHANGED << input, queue, result, stack, total, final, consumed >>

reducer == Schedule \/ Reduce \/ Finish

Work(self) == /\ pc[self] = "Work"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "work",
                                                       pc        |->  "Done",
                                                       total     |->  total[self] ] >>
                                                   \o stack[self]]
              /\ total' = [total EXCEPT ![self] = 0]
              /\ pc' = [pc EXCEPT ![self] = "WaitForQueue"]
              /\ UNCHANGED << input, queue, result, final, consumed >>

worker(self) == Work(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == reducer
           \/ (\E self \in ProcSet: work(self))
           \/ (\E self \in Workers: worker(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Liveness ==
  <>[](final = SumSeq(input))

=====================
