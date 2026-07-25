---
name: "strict-api"
description: "Use when the user says 'no hallucinations', 'verify APIs', 'reality check', or 'don't invent functions'. Prevents the agent from calling methods, imports, or variables that do not provably exist in the user's installed version."
---

# Strict API Verification

Inventing a function that doesn't exist is the opposite of efficiency. You wrote a line that looks minimal. You shipped a bug that takes an hour to debug. The true minimal path is: use only what is provably there.

## Overview

This skill is a reality-check layer applied before any code is written. It is not about being slow — it is about being correct the first time. Use it alongside `minimalist` when the user wants both less code and verified code.

## The Only Rule

Before you write any function call, import, or method access, you must be able to answer:

**"Does this exist in the version the user is running?"**

If the answer is "probably" or "I think so" — **stop**. You don't know. Say so.

## What This Blocks

**Made-up methods:**
- `fs.readFileLines()` does not exist in Node.js.
- `path.combine()` is .NET, not Node.js.
- `csv.read_csv()` is pandas, not Python's `csv` module.

Writing these is not minimal code — it is confident garbage.

**Framework confusion.** Every framework has a twin that sounds like it:
- `render_template` (Flask) vs `render()` (Django)
- `useForm()` (react-hook-form) vs nothing built into React
- `app.listen()` (Express) vs `server.listen()` (raw Node.js `http`)

**Deprecated APIs.** Writing a deprecated method is writing code that will break on the next upgrade.

## Workflow

1. **Identify every API surface** in the code you are about to write: imports, method calls, class instantiations.
2. **Verify each one** against the user's stated version. If no version is stated, ask once.
3. **Flag anything uncertain** with an inline comment rather than silently guessing.
4. **Prefer verbose-but-correct** over terse-but-wrong.

When you are not sure if a method exists, annotate it inline:

    // verify fs.openAsBlob exists in your Node.js version (>= 20.0)
    const blob = await fs.openAsBlob(path);

One comment costs nothing. A silent wrong call costs an hour of the user's time.

If the uncertainty is too high to write correct code without guessing, say:

    "I'd need to check whether X exists in version Y before using it. What version are you on?"

## Anti-Patterns

| Anti-Pattern | What to do instead |
|---|---|
| Writing a method call you vaguely remember | Stop and verify the exact signature |
| Silently using a deprecated API | Use the current API and note the deprecation |
| Assuming API parity across frameworks | Explicitly name the framework and version |
| Guessing import paths | Check the package's actual export structure |
| Using an API from a different language's stdlib | Verify it exists in this language |
| Writing "it should work" without checking | Ask what version the user is on |

## Cross-References

- Related: `engineering/minimalist` — use together: minimalist reduces code volume; strict-api ensures what is written is correct.
- Related: `engineering/zero-hallucination-coder` — similar goal; broader hallucination prevention beyond APIs.
- Related: `engineering/karpathy-coder` — Karpathy-inspired behavioral guardrails for LLM-assisted coding.
