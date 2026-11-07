---
name: content-language-gate
description: Scan product text (question banks, store copy, in-app strings) for forbidden language classes and count originality, then refuse to trust its own clean result unless it first caught known-bad samples. Use when auditing product copy before shipping, when a claim like "we never promise certainty" or "no fake percentages" needs to be proven rather than asserted, when preparing an App Review 4.3(b) originality argument, or when a text scanner reported zero violations and you want to know whether it can see at all.
---

# Content Language Gate

Scans product text against **your** forbidden-language classes and counts originality.
The classes live in a rule file, not in this skill — nothing product-specific is embedded.

## When to use it

- Auditing product copy before a release: question banks, generated text, store description.
- Turning a content rule ("no certainty claims", "no clinical diagnosis", "no fake
  percentages") from a stated intention into a measured gate.
- Building an **App Review 4.3(b)** argument: repeated strings are the signature of a
  template/copycat app, so the repeat count is evidence.

## When NOT to use it

- Tone and craft quality — this counts forbidden classes and duplicates, it does not have
  taste.
- Source code scanning — it reads text data.
- Localization review.

## Usage

```bash
scripts/language-gate.py <rules.json> [root-dir]
```

```json
{
  "forbidden": {"certainty": "\\b(definitely|guaranteed)\\b", "...": "..."},
  "decoys":    [["certainty", "This will definitely happen within two weeks."]],
  "content":   {"glob": "content/*.json", "fields": ["text", "short"],
                "list_fields": ["rules", "questions"], "option_field": "options"},
  "originality": [
    {"name": "output",   "fields": ["text", "short"], "mode": "pair", "gate": true},
    {"name": "headline", "fields": ["short"],         "mode": "each", "gate": false}
  ]
}
```

A runnable example with synthetic content is in `examples/`.
Exit code: `0` clean, `1` red.

## THREE PROPERTIES THAT MAKE IT TRUSTWORTHY

### 1. The gate tests itself every run

Before looking at real content it runs every `decoys` entry through its own patterns. If it
fails to catch them it prints `gate is BLIND` and **refuses to treat a clean result as
evidence**.

Measured reason: an earlier version of this gate matched a verb stem and mistook ordinary
phrases — "giving it room", "giving it time" — for clinical diagnosis, producing **8 false
violations**. It was writing its own defect onto the product. A scanner is a suspect too.

### 2. An empty scan is not a pass

If the content glob matches nothing, a naive gate reports "0 violations → clean". That is the
most common way a text gate lies: the rule file points at the wrong path and silence reads as
success. This one goes red with `NOTHING WAS SCANNED`.

### 3. Declare your unit of uniqueness — both defaults are wrong

Uniqueness means nothing until you say WHAT must be unique. I measured both failure
directions on the same content:

- **Merging blindly hides duplication.** A gate keying on `text + "|" + short` cannot see a
  repeated `short`, because `text` always differs — so the merged key always differs too.
- **Splitting blindly invents defects.** Counting bare fields surfaced "28 repeated
  headlines" and I recorded it as a hidden template-app defect. **It was not.** The product
  renders a headline **plus** a support line, and the design deliberately reuses one headline
  across three nuance variants:

```text
"You want to be seen where you are."  +  "Waiting to be noticed is not your way."
"You want to be seen where you are."  +  "You hope the word comes from others."
"You want to be seen where you are."  +  "You are waiting for the right moment."
```

  Measured: headline+support **pairs 286/286 unique (0 repeats)**; bare headlines 286/258
  (28 repeats). Two users can see the same headline; no user ever sees the same **output**.

So `originality` takes explicit units. `"gate": true` goes red on a repeat, `"gate": false`
is reported as `INFO`. Make the gated unit the thing the user actually receives.

## Acceptance

```text
SELF-TEST       : n/n decoys caught        -> gate is not blind
FORBIDDEN LANG  : N strings scanned        -> N must be > 0
                  violations=0
ORIGINALITY all : repeats=0
** LANGUAGE GATE CLEAN **
```

## Failure handling

| Output | Meaning |
|---|---|
| `gate is BLIND` | your `forbidden` patterns do not catch your own `decoys` — fix the **rules**, not the content |
| `NOTHING WAS SCANNED` | `content.glob` / `list_fields` are wrong |
| `Nx repeated ::` | a real duplicate; either vary the text or record why the repeat is intended |
| `[class] file id :: <text>` | a forbidden class matched — **first check whether the pattern is a false positive** |

That last row matters. Before writing a violation down as a product defect, test the pattern.
This gate's own history is the argument for it.

## Verification record

| Arm | Result |
|---|---|
| real content (≈1 100 strings, external rule file) | self-test 5/5 · violations 0 |
| originality, gated unit = output pair | **286/286 unique** on that content — clean at the unit that matters |
| originality, ungated unit = bare headline | 28 repeats reported as `INFO`, not as a verdict |
| **known-bad**: identical output emitted twice | **RED**, named the duplicated pair, exit `1` |
| design case: shared headline, distinct outputs | CLEAN, exit `0` |
| **empty scan** (wrong glob) | `NOTHING WAS SCANNED`, exit `1` — did **not** report clean |
| **blind rules** (patterns that match nothing) | declared **BLIND**, named every missed decoy |
