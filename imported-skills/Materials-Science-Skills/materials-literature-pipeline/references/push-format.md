# Push Format

Use this reference when formatting a daily or weekly literature digest for
Feishu, Telegram, email, Markdown inboxes, or other delivery channels.

The digest is for prioritization. It must preserve source-depth caveats and
cannot upgrade metadata or abstracts into manuscript evidence.

## Message Shape

```markdown
# {YYYY-MM-DD} Materials Literature Digest | {topic}

Scope: {material system}; {date window}; sources: {sources}
Screened: {screened_count}; deduplicated: {deduped_count}; delivered: top {n}

---

## #{rank} | {title}

{venue}, {year} | {authors} | score: {score_total}/100 | tier: {tier}
DOI/arXiv/link: {best_link}

One-line value: {specific reason this paper matters or should be deferred}

Method: {material system, method, characterization, model, or review type}

Key result: {specific result with conditions/units when available}

Evidence boundary: {what it can and cannot support at current source_depth}

Next action: {read | cite-gap-audit | monitor | exclude | archive}
```

## Field Rules

| Field | Rule |
|---|---|
| `One-line value` | Say why to open or defer the paper in one sentence. |
| `Method` | Include material system, test method, model, or review scope. |
| `Key result` | Prefer concrete data, conditions, or claims; avoid generic praise. |
| `Evidence boundary` | Preserve `metadata-only`, `abstract-screened`, `full-text-read`, or `data-extracted`. |
| `Next action` | Must match the candidate table. |

## Delivery Rules

- Do not force wiki/vault links into the push message. Archive links belong in
  notes or a later integration step.
- If a paper maps to a known author, lab, standard, or material-system thread,
  mention that naturally in the commentary.
- If delivery fails, save the Markdown digest and follow
  `degradation-strategy.md`.
