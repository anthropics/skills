# Example Session: Quantum Computing

## Invocation

```
/research-and-grill --deep quantum computing
```

## Research Summary (shown to user)

**Quantum Computing** — researched from 12 sources

Key concepts to be covered:
1. Superposition — how qubits differ from classical bits
2. Entanglement — what it enables and what it doesn't
3. Quantum interference — how it's used to amplify correct answers
4. Decoherence — the main engineering challenge
5. Quantum advantage — where quantum actually beats classical

*Ready to be grilled? Type 'yes' to start.*

---

## Grilling Session

**Q1:** Classical computers use bits that are 0 or 1. You said a qubit can be "both at once" — but when you measure it, you get one answer. So what's actually the computational advantage if you always collapse to a single outcome?

> *User:* The advantage is that during computation, before measurement, all states are explored simultaneously...

**Claude:** Exactly right — and this is where most explanations stop, which causes the misconception that quantum computers are just "trying all answers at once." But superposition alone isn't enough. What has to happen to the superposition *before* measurement to make the right answer more likely to come out?

> *User:* Some kind of... filtering?

**Claude:** Close — it's interference. The algorithm is designed so probability amplitudes for wrong answers cancel out (destructive interference) and the right answer's amplitude reinforces (constructive interference). That's why quantum algorithms are so hard to design — you have to engineer the interference. With that in mind: why can't you use a quantum computer to speed up *every* problem?

---

## Mastery Report

**Strong understanding:** Superposition, quantum advantage framing  
**Worth revisiting:** Interference mechanics, why decoherence is hard to solve  
**Recommended next:** Nielsen & Chuang Ch.1, Scott Aaronson's "Quantum Computing Since Democritus"
