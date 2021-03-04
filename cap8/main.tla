---- MODULE main ----

EXTENDS Integers, TLC, FiniteSets

CONSTANTS Nodes, NULL

INSTANCE LinkedLists WITH NULL <- NULL

AllLinkedLists == LinkedLists(Nodes)

CyclicLLExistence ==
  \E ll \in AllLinkedLists: Cyclic(ll)

AcyclicLLExistence ==
  \E ll \in AllLinkedLists: ~Cyclic(ll)

RingCoverage ==
  \A node_subset \in SUBSET Nodes \ {{}}:
    Assert(
      \E ll \in AllLinkedLists:
        /\ Ring(ll)
        /\ DOMAIN ll = node_subset,
      <<"Counterexample:", node_subset>>
           )

\* there should be at most one node without a parent, i.e., another
\* node pointing to it.
AtMostOneOrphan(ll) ==
  Cardinality({n \in Range(ll) : n \notin DOMAIN ll}) \in 0..1

CycleEqualsTwoParents(ll) ==
  Cyclic(ll) <=>
    \/
       /\ Ring(ll)
       /\ ~\E n \in Range(ll):
            Cardinality(Parents(ll, n)) = 2
    \/ \E n \in Range(ll):
         Cardinality(Parents(ll, n)) = 2

NoMoreThanTwoParents(ll) ==
  ~\E n \in Range(ll):
    Cardinality(Parents(ll, n)) > 2

Valid ==
  /\ CyclicLLExistence
  /\ AcyclicLLExistence
  /\ RingCoverage
  /\ \A ll \in AllLinkedLists:
       /\ Assert(AtMostOneOrphan(ll), <<"Counterexample:", ll>>)
       /\ Assert(CycleEqualsTwoParents(ll), <<"Counterexample:", ll>>)
       /\ Assert(NoMoreThanTwoParents(ll), <<"Counterexample:", ll>>)

=====================
