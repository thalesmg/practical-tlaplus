---- MODULE LinkedLists ----

CONSTANT NULL
LOCAL INSTANCE TLC \* Assert

PointerMaps(Nodes) == [Nodes -> Nodes \union {NULL}]

Range(f) == {f[i] : i \in DOMAIN f}

IsLinkedList(PointerMap) ==
  LET
    nodes == DOMAIN PointerMap
    all_seqs == [1..Cardinality(nodes) |-> nodes]
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

LinkedLists(Nodes) ==
  IF NULL \in Nodes THEN Assert(FALSE, "NULL não pode estar entre os nós") ELSE
    {pm \in PointerMaps(Nodes) : IsLinkedList(pm)}

============================
