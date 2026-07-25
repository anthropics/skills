# Output format (writing)

Return every draft in this six-part structure. The structure is designed to keep evidence visible, revision cheap, and handoffs clean.

For `compose`, `revise`, `hybrid`, or `qa` state-machine runs, prepend a
compact status block before the six-part draft:

```text
State: compose / revise / hybrid / qa
Artifact: path or pasted text label
Score/status: average score and pass / revise / stop
Remaining risks: highest-risk evidence, method, argument, or language issue
Stop/continue reason: stopping rule or next revision target
Next action: one concrete action only
```

The status block does not replace the six-part structure. It records the
project loop so the next run can update `state.json` honestly.

## 1. Draft

The requested prose. Each paragraph carries one message only. The first sentence of each paragraph forecasts its message. Placeholders mark missing evidence instead of inventing content.

## 2. Section outline

3-7 compact bullets when the task involves a full section. Each bullet states the paragraph message (context, gap, approach, result, comparison, mechanism, implication, limitation) and the evidence it rests on. This makes reverse-outlining automatic.

## 3. Assumptions

Only material issues; do not pad with style nits. List every inference made without direct evidence, every missing experimental input, and every placeholder left in the draft. Keep each entry actionable.

## 4. Claim-evidence map

For major claims, use the form:

```text
Claim: ... | Evidence: ... | Status: supported / needs evidence / inferred
```

If a claim has no evidence, mark it `needs evidence` and echo the placeholder used in the draft. Do not downgrade the status to make the draft look more complete.

## 5. Why this structure

2-4 short bullets on the structural choices made: why this paragraph order, why this claim-evidence pairing, why this boundary is stated where it is.

## 6. To redirect me

One line inviting targeted feedback, e.g. "Name the paragraph or claim that is off and I will revise only that, keeping the rest." This sets up the targeted revision loop (workflow stage 5f) instead of a full rewrite.

---

## Language convention

- Chinese input → Chinese output.
- English input → English output.
- Mixed input → follow the user's main language; keep technical terms in their canonical form from the Terminology Ledger.

## Placeholder rule

If essential evidence or boundary is missing, do not invent. Write a placeholder such as `[TO CONFIRM: comparator group strength at 28 days]` and list it under `Assumptions:` and `Claim-evidence map` with status `needs evidence`.

## Revision output

When the user asks for a revision, preserve the same six-part structure. Keep the unchanged paragraphs verbatim, mark the changed paragraphs, and update only the assumptions and claim-evidence map entries that are affected.
