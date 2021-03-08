---- MODULE door ----

EXTENDS TLC

(*--algorithm door

variables
  open = FALSE,
  locked = FALSE;

begin
  Event:
    either \* unlock
      await locked;
      locked := FALSE;
    or \* lock
      await ~locked;
      locked := TRUE;
    or \* close
      await open;
      open := FALSE;
    or \* open
      await ~locked;
      await ~open;
      open := TRUE;
    end either;
  goto Event;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "ac13ecb0" /\ chksum(tla) = "1233f4c8")
VARIABLES open, locked, pc

vars == << open, locked, pc >>

Init == (* Global variables *)
        /\ open = FALSE
        /\ locked = FALSE
        /\ pc = "Event"

Event == /\ pc = "Event"
         /\ \/ /\ locked
               /\ locked' = FALSE
               /\ open' = open
            \/ /\ ~locked
               /\ locked' = TRUE
               /\ open' = open
            \/ /\ open
               /\ open' = FALSE
               /\ UNCHANGED locked
            \/ /\ ~locked
               /\ ~open
               /\ open' = TRUE
               /\ UNCHANGED locked
         /\ pc' = "Event"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Event
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=====================
