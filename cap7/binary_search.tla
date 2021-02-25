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

(*--algorithm binary_search
variables
  i = 1,
  seq \in OrderedSeqOf(1..MaxInt, MaxInt),
  low = 1,
  high = Len(seq),
  target \in 1..MaxInt,
  found_index = 0,
  counter = 0;

begin
  Search:
    while low <= high do
      counter := counter + 1;
      with
        lh = high - low,
        m = high - (lh \div 2)
      do
        assert lh <= MaxInt;
        if seq[m] = target then
          found_index := m;
          goto Result;
        elsif seq[m] > target then
          high := m - 1;
        else
          low := m + 1;
        end if;
      end with;
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
\* BEGIN TRANSLATION (chksum(pcal) = "d5abfffb" /\ chksum(tla) = "a87929a5")
VARIABLES i, seq, low, high, target, found_index, counter, pc

vars == << i, seq, low, high, target, found_index, counter, pc >>

Init == (* Global variables *)
        /\ i = 1
        /\ seq \in OrderedSeqOf(1..MaxInt, MaxInt)
        /\ low = 1
        /\ high = Len(seq)
        /\ target \in 1..MaxInt
        /\ found_index = 0
        /\ counter = 0
        /\ pc = "Search"

Search == /\ pc = "Search"
          /\ IF low <= high
                THEN /\ counter' = counter + 1
                     /\ LET lh == high - low IN
                          LET m == high - (lh \div 2) IN
                            /\ Assert(lh <= MaxInt, 
                                      "Failure of assertion at line 41, column 9.")
                            /\ IF seq[m] = target
                                  THEN /\ found_index' = m
                                       /\ pc' = "Result"
                                       /\ UNCHANGED << low, high >>
                                  ELSE /\ IF seq[m] > target
                                             THEN /\ high' = m - 1
                                                  /\ low' = low
                                             ELSE /\ low' = m + 1
                                                  /\ high' = high
                                       /\ pc' = "Search"
                                       /\ UNCHANGED found_index
                ELSE /\ pc' = "Result"
                     /\ UNCHANGED << low, high, found_index, counter >>
          /\ UNCHANGED << i, seq, target >>

Result == /\ pc = "Result"
          /\ IF target \in Range(seq)
                THEN /\ Assert(seq[found_index] = target, 
                               "Failure of assertion at line 54, column 7.")
                ELSE /\ Assert(found_index = 0, 
                               "Failure of assertion at line 56, column 7.")
          /\ IF Len(seq) > 0
                THEN /\ Assert(Pow2(counter - 1) <= Len(seq), 
                               "Failure of assertion at line 60, column 7.")
                ELSE /\ TRUE
          /\ pc' = "Done"
          /\ UNCHANGED << i, seq, low, high, target, found_index, counter >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Search \/ Result
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

==============================
