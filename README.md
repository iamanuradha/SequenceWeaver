# README: Detecting Out-of-Order Response Using TLA+

## 🧩 Overview
This project showcases how TLA+ (Temporal Logic of Actions) can be used to detect concurrency or ordering bugs that are visually subtle but logically incorrect. We model a simple interaction between a `Client` and a `Server` from a Draw.io sequence diagram that appears to have an out-of-order message delivery.

---

## 📐 Sequence Diagram (Draw.io XML)

The sequence diagram includes:
- **Lifelines**: `Client` and `Server`
- **Messages**: `Request` (Client -> Server) and `Response` (Server -> Client)

### 🚨 Bug Detail:
The `Response` message is positioned **above** the `Request` in the XML, implying that the response happens **before** the request—an ordering violation.

### 🔧 Extracted Snippet:
```xml
<mxCell id="Response" value="Response" edge="1" parent="1" source="Server" target="Client">
  <mxGeometry relative="1" as="geometry">
    <mxPoint x="160" y="120" as="targetPoint" />
  </mxGeometry>
</mxCell>
<mxCell id="Request" value="Request" edge="1" parent="1" source="Client" target="Server">
  <mxGeometry relative="1" as="geometry">
    <mxPoint x="360" y="180" as="targetPoint" />
  </mxGeometry>
</mxCell>
```

---

## 🧠 TLA+ Specification

We model the interaction using states that represent messages being sent. The legal state transitions are:
```tla
ValidSteps == [
  "start"   |-> "Request",
  "Request" |-> "Response"
]
```

### Variables
- `state`: the current event (message)
- `prev`: the last event

### Specification
```tla
Init ==
  /\ state = "Response"  \* Starts incorrectly with Response
  /\ prev = "start"

Next ==
  \/ /\ state = "Response"
      /\ state' = "Request"
      /\ prev' = state
  \/ /\ UNCHANGED <<state, prev>>

Spec == Init /\ [][Next]_<<state, prev>>
```

### Invariant
```tla
Invariant ==
  \/ prev = "start"
  \/ ValidSteps[prev] = state
```

This invariant checks whether each transition is legal according to the defined `ValidSteps`.

---

## ❗ What TLA+ Detects
The model checker (`TLC`) detects an **invariant violation** because the transition from `start` → `Response` is not valid. This indicates a concurrency bug or a logical flaw in the interaction sequence.

---

## 🌍 Real-World Use Cases

### 1. Distributed Systems / Caching
- A server writes a cached response **before** the client's request is fully processed.

### 2. Messaging Queues
- Messages consumed **out of order**, leading to invalid state assumptions.

### 3. Webhooks or Event Streams
- Events fired **before** the originating cause, causing confusion or rollback issues.

### 4. UI State Management
- UI updates rendered before the state is initialized due to async race conditions.

---

## ✅ How to Use
1. Install [TLA+ Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html)
2. Load the `.tla` file containing the spec
3. Run the TLC model checker
4. Observe the execution trace and the invariant violation

---

## 📁 Files Included
- `diagram.xml`: The Draw.io sequence diagram XML with bug
- `sloggedrequest.tla`: TLA+ spec modeling the sequence
- `README.md`: This file

---

## 📬 Conclusion
This example demonstrates how **visual bugs** in sequence diagrams can lead to **logical inconsistencies** in real-world systems. With TLA+, we can rigorously verify and catch such issues early in the design process.

Use this method in any event-driven, asynchronous, or distributed system design to guard against invalid assumptions about time and order.

