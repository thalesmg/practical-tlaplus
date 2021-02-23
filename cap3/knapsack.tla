------------------------------ MODULE knapsack ------------------------------

EXTENDS TLC, Integers, Sequences
CONSTANTS Capacity, Items, ValueRange, SizeRange

ASSUME Capacity > 0
ASSUME SizeRange \subseteq 1..Capacity
ASSUME \A v \in ValueRange: v >= 0

PT == INSTANCE PT

(*Capacity == 7
Items == {"a", "b", "c"}
*)
ItemParams == [size: SizeRange, value: ValueRange]
ItemSets == [Items -> ItemParams]

KnapsackSize(sack, itemset) ==
  LET size_for(item) == itemset[item].size * sack[item]
  IN PT!ReduceSet(LAMBDA item, acc: size_for(item) + acc, Items, 0)

ValidKnapsacks(itemset) ==
  {sack \in [Items -> 0..4]: KnapsackSize(sack, itemset) <= Capacity}

KnapsackValue(sack, itemset) ==
  LET value_for(item) == itemset[item].value * sack[item]
  IN PT!ReduceSet(LAMBDA item, acc: value_for(item) + acc, Items, 0)

BestKnapsack(itemset) ==
  LET all == ValidKnapsacks(itemset)
  IN CHOOSE best \in all:
    \A worse \in all \ {best}:
    KnapsackValue(best, itemset) > KnapsackValue(worse, itemset)

BestKnapsacksOne(itemset) ==
  LET all == ValidKnapsacks(itemset)
  IN
    CHOOSE all_the_best \in SUBSET all:
      \A good \in all_the_best:
        /\ CHOOSE other \in all_the_best:
          KnapsackValue(other, itemset) = KnapsackValue(good, itemset)
        /\ CHOOSE worse \in all \ all_the_best:
          KnapsackValue(worse, itemset) < KnapsackValue(good, itemset)

BestKnapsacksTwo(itemset) ==
  LET
    all == ValidKnapsacks(itemset)
    best == CHOOSE best \in all:
      \A worse \in all \ {best}:
        KnapsackValue(best, itemset) >= KnapsackValue(worse, itemset)
    value_of_best == KnapsackValue(best, itemset)
  IN
    {k \in all: KnapsackValue(k, itemset) = value_of_best}

BestKnapsacks(itemset) ==
  LET
    value(sack) == KnapsackValue(sack, itemset)
    all == ValidKnapsacks(itemset)
    best == CHOOSE best \in all:
      \A worse \in all \ {best}:
        value(best) >= value(worse)
  IN
    {k \in all: value(k) = value(best)}

(*--algorithm debug
variables itemset \in ItemSets
begin
  \* assert BestKnapsack(itemset) \in ValidKnapsacks(itemset)
  \* assert BestKnapsacksOne(itemset) \subseteq ValidKnapsacks(itemset)
  assert BestKnapsacks(itemset) \subseteq ValidKnapsacks(itemset)
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "c0d11dc1" /\ chksum(tla) = "45b82017")
VARIABLES itemset, pc

vars == << itemset, pc >>

Init == (* Global variables *)
        /\ itemset \in ItemSets
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(BestKnapsacksOne(itemset) \subseteq ValidKnapsacks(itemset),
                   "Failure of assertion at line 69, column 3.")
         /\ pc' = "Done"
         /\ UNCHANGED itemset

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Feb 18 09:28:17 BRT 2021 by thales
\* Created Mon Jan 07 12:24:55 BRST 2019 by thales
