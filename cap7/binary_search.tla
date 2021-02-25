---- MODULE binary_search ----

EXTENDS TLC, Integers, Sequences

PT == INSTANCE PT

OrderedSeqOf(set, n) ==
  { seq \in PT!SeqOf(set, n):
    \A x \in 2..Len(seq):
      seq[x] >= seq[x - 1] }

MaxInt == 4
Range(f) == {f[x]: x \in DOMAIN f}

Pow2(n) ==
  LET
    f[x \in 0..n] ==
      IF x = 0
      THEN 1
      ELSE 2 * f[x - 1]
  IN f[n]

(*--algorithm definetively_binary_search
variables
  i = 1,
  seq \in OrderedSeqOf(1..MaxInt, MaxInt),
  target \in 1..MaxInt,
  found_index = 0,
  counter = 0;

begin
  Search:
    while i <= Len(seq) do
      counter := counter + 1;
      if seq[i] = target then
        found_index := i;
        goto Result;
      else
        i := i + 1;
      end if;
    end while;
  Result:
    if target \in Range(seq) then
      assert seq[found_index] = target;
    else
      assert found_index = 0;
    end if;
    \* if the algorithm is O(log2(n))...
    if Len(seq) > 0 then
      assert Pow2(counter - 1) <= Len(seq);
    end if;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "623ed8c5" /\ chksum(tla) = "383b1072")
VARIABLES i, seq, target, found_index, counter, pc

vars == << i, seq, target, found_index, counter, pc >>

Init == (* Global variables *)
        /\ i = 1
        /\ seq \in OrderedSeqOf(1..MaxInt, MaxInt)
        /\ target \in 1..MaxInt
        /\ found_index = 0
        /\ counter = 0
        /\ pc = "Search"

Search == /\ pc = "Search"
          /\ IF i <= Len(seq)
                THEN /\ counter' = counter + 1
                     /\ IF seq[i] = target
                           THEN /\ found_index' = i
                                /\ pc' = "Result"
                                /\ i' = i
                           ELSE /\ i' = i + 1
                                /\ pc' = "Search"
                                /\ UNCHANGED found_index
                ELSE /\ pc' = "Result"
                     /\ UNCHANGED << i, found_index, counter >>
          /\ UNCHANGED << seq, target >>

Result == /\ pc = "Result"
          /\ IF target \in Range(seq)
                THEN /\ Assert(seq[found_index] = target, 
                               "Failure of assertion at line 44, column 7.")
                ELSE /\ Assert(found_index = 0, 
                               "Failure of assertion at line 46, column 7.")
          /\ IF Len(seq) > 0
                THEN /\ Assert(Pow2(counter - 1) <= Len(seq), 
                               "Failure of assertion at line 50, column 7.")
                ELSE /\ TRUE
          /\ pc' = "Done"
          /\ UNCHANGED << i, seq, target, found_index, counter >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Search \/ Result
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

==============================
