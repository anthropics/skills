# Description Optimization Reference

Use this after the skill itself is in good shape.

## Goal

The `description` field in SKILL.md frontmatter is the primary trigger mechanism. After building or improving a skill, offer to optimize the description so Claude consults it in the right situations.

## Step 1: Generate trigger eval queries

Create around 20 realistic queries, mixing should-trigger and should-not-trigger cases.

```json
[
  {"query": "the user prompt", "should_trigger": true},
  {"query": "another prompt", "should_trigger": false}
]
```

Guidance:
- make the queries look like real user asks, not toy phrases
- include detail, ambiguity, typos, shorthand, and edge cases
- cover competing skills and near-misses
- avoid obviously irrelevant negatives

## Step 2: Review the eval set with the user

Use `assets/eval_review.html`:
1. read the template
2. replace the placeholders for eval JSON, skill name, and current description
3. write it to a temp HTML file
4. open it for the user
5. after export, read the newest `eval_set.json` from Downloads

This step matters because poor eval queries lead to poor descriptions.

## Step 3: Run the optimization loop

Run the optimization in the background:

```bash
python -m scripts.run_loop \
  --eval-set <path-to-trigger-eval.json> \
  --skill-path <path-to-skill> \
  --model <model-id-powering-this-session> \
  --max-iterations 5 \
  --verbose
```

Use the current session's model ID so the test matches the user's real trigger behavior.

The loop evaluates the current description, proposes revisions, and scores them on both train and held-out test queries. Give the user occasional progress updates while it runs.

## How triggering works

Claude only consults a skill when it would actually help. Very simple tasks often will not trigger a skill even if the description matches, because Claude can already solve them directly. So the eval queries must be substantive enough that a skill would genuinely add value.

## Step 4: Apply the best result

Take `best_description` from the output JSON, update the frontmatter, then show the user the before/after text and the score change.
