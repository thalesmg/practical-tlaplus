------------------------------ MODULE knapsack ------------------------------

EXTENDS TLC, Integers, Sequences

PT == INSTANCE PT

Capacity == 7
Items == {"a", "b", "c"}
ItemParams == [size: 2..4, value: 0..5]
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
  assert BestKnapsack(itemset) \in ValidKnapsacks(itemset);
end algorithm; *)

=============================================================================
\* Modification History
\* Last modified Mon Jan 07 12:54:59 BRST 2019 by thales
\* Created Mon Jan 07 12:24:55 BRST 2019 by thales
