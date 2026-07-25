# Karpathy Principles — Full Context

Source: [Andrej Karpathy on X](https://x.com/karpathy/status/2015883857489522876), January 2026.

## The original observations

Karpathy identified four categories of LLM coding failure:

### 1. Assumption management

> "The models make wrong assumptions on your behalf and just run along with them without checking. They don't manage their confusion, don't seek clarifications, don't surface inconsistencies, don't present tradeoffs, don't push back when they should."

**What this means in practice:**
- User says "export user data" → LLM picks JSON, writes to disk, includes all fields, doesn't ask which users
- User says "make it faster" → LLM adds caching, async, and connection pooling without asking what "faster" means
- User says "fix the bug" → LLM guesses which bug based on context, never confirms

**The fix:** Before writing ANY code, list assumptions explicitly. If there are 2+ valid interpretations, present them and ask. If something is unclear, stop and name the confusion.

### 2. Overcomplexity

> "They really like to overcomplicate code and APIs, bloat abstractions, don't clean up dead code... implement a bloated construction over 1000 lines when 100 would do."

**Why LLMs do this:**
- Training data contains enterprise patterns (Strategy, Factory, Observer) applied at inappropriate scale
- "More thorough" feels safe — the LLM can't be wrong for handling edge cases, even if they're impossible
- No cost pressure — generating 1000 lines takes the same effort as generating 100

**The fix:** Ask "would a senior engineer say this is overcomplicated?" after writing. If a function has one caller, it shouldn't be a class. If an abstraction serves one use case, inline it.

### 3. Orthogonal edits

> "They still sometimes change/remove comments and code they don't sufficiently understand as side effects, even if orthogonal to the task."

**Common manifestations:**
- Reformats quote style while fixing a bug
- Adds type annotations to unchanged functions
- "Improves" a comment near the bug fix
- Renames variables in untouched code
- Adds docstrings to functions that weren't changed

**The fix:** Every changed line must trace to the user's request. If you notice something unrelated that could be improved, mention it — don't change it.

### 4. Weak verification loops

> "LLMs are exceptionally good at looping until they meet specific goals... Don't tell it what to do, give it success criteria and watch it go."

**The insight:** LLMs perform dramatically better with declarative goals ("all tests pass") than imperative instructions ("add a try/except block"). The best workflow:

1. Define success criteria as concrete, verifiable checks
2. Let the LLM loop until all checks pass
3. Each step has its own "verify:" annotation

## When to relax each principle

| Principle | Relax when... |
|---|---|
| Think Before Coding | The request is unambiguous and self-contained (e.g., "add a return statement on line 42") |
| Simplicity First | The user explicitly asked for an abstraction, configuration, or extensibility |
| Surgical Changes | The user said "refactor this file" or "clean up this module" |
| Goal-Driven Execution | The task is a one-liner with obvious correctness (e.g., rename a variable) |

## The 80/20 of enforcement

If you adopt only ONE principle, adopt **Surgical Changes** (#3). It's the most measurable (diff analysis), the most commonly violated (LLMs love to "improve" things), and the easiest to check (does the diff contain lines unrelated to the task?).

If you adopt TWO, add **Simplicity First** (#2). Overcomplexity is the second-most-common failure and the most expensive to fix (you ship abstraction debt, then maintain it forever).
