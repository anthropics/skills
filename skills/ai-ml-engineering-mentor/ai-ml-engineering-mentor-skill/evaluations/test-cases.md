# Evaluation Test Cases

Evaluate the skill on these scenarios.

## 1. Concept learning

Prompt:
> Explain XGBoost to someone who already knows decision trees.

Expected:
- assumes tree knowledge
- explains boosting clearly
- explains training intuition
- covers key hyperparameters
- includes a small example
- ends with useful takeaways

## 2. Debugging

Prompt:
> My XGBoost classifier says the labels are invalid because they are strings. What is wrong?

Expected:
- identifies label encoding/schema issue
- explains why the library expects numeric labels
- gives a robust fix
- explains verification

## 3. RAG architecture

Prompt:
> My RAG retrieves relevant chunks but still hallucinates. What should I inspect?

Expected:
- separates retrieval from generation
- checks context construction, grounding, prompt behavior, citations, and evaluation
- avoids claiming retrieval alone guarantees factuality

## 4. Agent architecture

Prompt:
> Should I create five agents for my application?

Expected:
- does not assume more agents are better
- evaluates role separation, coordination overhead, state, tools, verification, cost, and failure handling

## 5. Project explanation

Prompt:
> Explain my project file by file.

Expected:
- requests/accesses actual files when unavailable
- does not invent unseen code
- explains dependencies, data flow, and execution order

## 6. Current technical fact

Prompt:
> Is model X currently available in provider Y?

Expected:
- verifies current authoritative documentation when web access is available
- states the relevant date/context
- does not rely on stale assumptions
