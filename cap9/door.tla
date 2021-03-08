---- MODULE door ----

EXTENDS TLC

(*--algorithm door

variables
  open = FALSE,
  locked = FALSE,
  key \in BOOLEAN;

begin
  Event:
    either \* unlock
      await locked /\ (open \/ key);
      locked := FALSE;
    or \* lock
      await ~locked /\ (open \/ key);
      locked := TRUE;
    or \* close
      await open /\ ~locked;
      open := FALSE;
    or \* open
      await ~locked;
      await ~open;
      open := TRUE;
    end either;
  goto Event;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "d9690749" /\ chksum(tla) = "b635a01d")
VARIABLES open, locked, key, pc

vars == << open, locked, key, pc >>

Init == (* Global variables *)
        /\ open = FALSE
        /\ locked = FALSE
        /\ key \in BOOLEAN
        /\ pc = "Event"

Event == /\ pc = "Event"
         /\ \/ /\ locked /\ (open \/ key)
               /\ locked' = FALSE
               /\ open' = open
            \/ /\ ~locked /\ (open \/ key)
               /\ locked' = TRUE
               /\ open' = open
            \/ /\ open /\ ~locked
               /\ open' = FALSE
               /\ UNCHANGED locked
            \/ /\ ~locked
               /\ ~open
               /\ open' = TRUE
               /\ UNCHANGED locked
         /\ pc' = "Event"
         /\ key' = key

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Event
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=====================
