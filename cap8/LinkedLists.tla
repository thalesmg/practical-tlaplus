---- MODULE LinkedLists ----

CONSTANT NULL

LOCAL INSTANCE TLC \* Assert
LOCAL INSTANCE FiniteSets \* Cardinality
LOCAL INSTANCE Sequences \* Len
LOCAL INSTANCE Integers \* ..

\* conjunto de funções
PointerMaps(Nodes) == [Nodes -> Nodes \union {NULL}]

Range(f) == {f[i] : i \in DOMAIN f}

IsLinkedList(PointerMap) ==
  LET
    nodes == DOMAIN PointerMap
    all_seqs == [1..Cardinality(nodes) -> nodes]
  IN
    \E ordering \in all_seqs:
      \* cada nó aponta para o próximo na ordenação
      /\ \A i \in 1..Len(ordering) - 1:
           \* não forçamos terminar em NULL para permitir ciclos
           PointerMap[ordering[i]] = ordering[i + 1]
      \* cada nó aparece exatamente uma vez na ordenação
      /\ nodes \subseteq Range(ordering)
      \* /\ \A node \in nodes:
      \*      node
      \*      \E i \in 1..Len(ordering):
      \*         ordering[i] = node

Ring(LL) == (DOMAIN LL = Range(LL))

\* First(LL) ==
\*   IF Ring(LL)
\*   THEN CHOOSE n \in DOMAIN LL: TRUE
\*   ELSE CHOOSE n \in DOMAIN LL: n \notin Range(LL)

First(LL) ==
  CHOOSE n \in DOMAIN LL:
    ~Ring(LL) => n \notin Range(LL)

Cyclic(LL) == NULL \notin Range(LL)

LinkedLists(Nodes) ==
  IF NULL \in Nodes THEN Assert(FALSE, "NULL não pode estar entre os nós") ELSE
    LET
      node_subsets == SUBSET Nodes \ {{}}
      \* conjunto de conjunto de funções
      pointer_maps_sets == {PointerMaps(subset) : subset \in node_subsets}
      \* conjunto de funções
      all_pointer_maps == UNION pointer_maps_sets
    IN
      {pm \in all_pointer_maps : IsLinkedList(pm)}

============================
