------------------------------- MODULE cache -------------------------------

EXTENDS Integers
CONSTANTS ResourceCap, MaxConsumerReq, Actors

ASSUME ResourceCap > 0
ASSUME MaxConsumerReq \in 1..ResourceCap
ASSUME Actors /= {}

(*--algorithm cache
variables
  resources_cap \in 1..ResourceCap,
  resources_left = resources_cap,
  reserved = 0;

define
  ResourceInvariant == resources_left >= 0
end define;

process actor \in Actors
variables
  resources_needed \in 1..MaxConsumerReq
begin
  WaitForResources:
    while TRUE do
      await reserved + resources_needed <= resources_left;
      reserved := reserved + resources_needed;
      UseResources:
        while resources_needed > 0 do
          resources_left := resources_left - 1;
          resources_needed := resources_needed - 1;
          reserved := reserved - 1;
        end while;
        with x \in 1..MaxConsumerReq do
          resources_needed := x;
        end with;
    end while;
end process;

process time = "time"
begin
  Tick:
    resources_left := resources_cap;
    goto Tick;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "31cdd6fd" /\ chksum(tla) = "abe69fa1")
VARIABLES resources_cap, resources_left, reserved, pc

(* define statement *)
ResourceInvariant == resources_left >= 0

VARIABLE resources_needed

vars == << resources_cap, resources_left, reserved, pc, resources_needed >>

ProcSet == (Actors) \cup {"time"}

Init == (* Global variables *)
        /\ resources_cap \in 1..ResourceCap
        /\ resources_left = resources_cap
        /\ reserved = 0
        (* Process actor *)
        /\ resources_needed \in [Actors -> 1..MaxConsumerReq]
        /\ pc = [self \in ProcSet |-> CASE self \in Actors -> "WaitForResources"
                                        [] self = "time" -> "Tick"]

WaitForResources(self) == /\ pc[self] = "WaitForResources"
                          /\ reserved + resources_needed[self] <= resources_left
                          /\ reserved' = reserved + resources_needed[self]
                          /\ pc' = [pc EXCEPT ![self] = "UseResources"]
                          /\ UNCHANGED << resources_cap, resources_left, 
                                          resources_needed >>

UseResources(self) == /\ pc[self] = "UseResources"
                      /\ IF resources_needed[self] > 0
                            THEN /\ resources_left' = resources_left - 1
                                 /\ resources_needed' = [resources_needed EXCEPT ![self] = resources_needed[self] - 1]
                                 /\ reserved' = reserved - 1
                                 /\ pc' = [pc EXCEPT ![self] = "UseResources"]
                            ELSE /\ \E x \in 1..MaxConsumerReq:
                                      resources_needed' = [resources_needed EXCEPT ![self] = x]
                                 /\ pc' = [pc EXCEPT ![self] = "WaitForResources"]
                                 /\ UNCHANGED << resources_left, reserved >>
                      /\ UNCHANGED resources_cap

actor(self) == WaitForResources(self) \/ UseResources(self)

Tick == /\ pc["time"] = "Tick"
        /\ resources_left' = resources_cap
        /\ pc' = [pc EXCEPT !["time"] = "Tick"]
        /\ UNCHANGED << resources_cap, reserved, resources_needed >>

time == Tick

Next == time
           \/ (\E self \in Actors: actor(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Feb 23 08:28:27 BRT 2021 by thales
\* Created Wed Jan 09 13:28:05 BRST 2019 by thales
