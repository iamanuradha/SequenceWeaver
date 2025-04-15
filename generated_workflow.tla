---- MODULE generated_workflow ----
EXTENDS Sequences, Integers, TLC

CONSTANT MAX_LEN

VARIABLES state, messages

Init ==
  /\ state = "Service"
  /\ messages = << >>

(* Actions with bounded messages *)
Action_0 ==
  /\ state = "Service"
  /\ Len(messages) < MAX_LEN
  /\ state' = "Client"
  /\ messages' = Append(messages, "Response")

Action_1 ==
  /\ state = "Client"
  /\ Len(messages) < MAX_LEN
  /\ state' = "Service"
  /\ messages' = Append(messages, "Request")

Next == Action_0 \/ Action_1

SelectIndex(seq, msg) ==
  IF \E i \in 1..Len(seq): seq[i] = msg
  THEN CHOOSE i \in 1..Len(seq): seq[i] = msg
  ELSE -1

(* Invariant: Request must appear before Response *)
Invariant ==
  LET r1 == SelectIndex(messages, "Response") IN
  LET r0 == SelectIndex(messages, "Request") IN
    r1 = -1 \/ (r0 # -1 /\ r0 < r1)

Spec == Init /\ [][Next]_<<state, messages>> /\ Invariant

====
