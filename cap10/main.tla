---- MODULE main ----

EXTENDS TLC, Integers, Sequences

CONSTANTS Books, People, NumCopies

ASSUME NumCopies \subseteq Nat

PT == INSTANCE PT

set ++ x == set \union {x}
set -- x == set \ {x}

(*--algorithm library

variables
  library \in [Books -> NumCopies];

define
  AvailableBooks == {b \in Books : library[b] > 0}
end define;

fair process person \in People
variables
  books = {},
  wants \in SUBSET Books;
begin
  Person:
    either
      \* Checkout:
      with b \in AvailableBooks do
        library[b] := library[b] - 1;
        books := books ++ b;
        wants := wants -- b;
      end with;
    or
      \* Return:
      with b \in books do
        library[b] := library[b] + 1;
        books := books -- b;
      end with;
    end either;
  goto Person;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "e4f64774" /\ chksum(tla) = "929b132")
VARIABLES library, pc

(* define statement *)
AvailableBooks == {b \in Books : library[b] > 0}

VARIABLES books, wants

vars == << library, pc, books, wants >>

ProcSet == (People)

Init == (* Global variables *)
        /\ library \in [Books -> NumCopies]
        (* Process person *)
        /\ books = [self \in People |-> {}]
        /\ wants \in [People -> SUBSET Books]
        /\ pc = [self \in ProcSet |-> "Person"]

Person(self) == /\ pc[self] = "Person"
                /\ \/ /\ \E b \in AvailableBooks:
                           /\ library' = [library EXCEPT ![b] = library[b] - 1]
                           /\ books' = [books EXCEPT ![self] = books[self] ++ b]
                           /\ wants' = [wants EXCEPT ![self] = wants[self] -- b]
                   \/ /\ \E b \in books[self]:
                           /\ library' = [library EXCEPT ![b] = library[b] + 1]
                           /\ books' = [books EXCEPT ![self] = books[self] -- b]
                      /\ wants' = wants
                /\ pc' = [pc EXCEPT ![self] = "Person"]

person(self) == Person(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in People: person(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in People : WF_vars(person(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

TypeInvariant ==
     \* no negative count nor greater than the maximum
  /\ library \in [Books -> NumCopies ++ 0]
     \* people can only carry Books
  /\ books \in [People -> SUBSET Books]
     \* people can only want Books
  /\ wants \in [People -> SUBSET Books]

Liveness ==
  /\ <>(\A p \in People : wants[p] = {})

=====================
