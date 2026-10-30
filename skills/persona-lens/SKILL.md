---
name: persona-lens
description: "Taste + DTC-playbook intelligence layer. A registry of decomposable 'lenses' — thought-leader perspectives (Steve Jobs, Rick Rubin, Hormozi, Dieter Rams, etc.) and brand-funnel playbooks (Huel, Hims, AG1, Oura, Gymshark, etc.) — that you can apply, fuse, and digest into the 底层逻辑 (first-principles) of a creative space. Each lens stores a 12-30 field decomposition: pillars, frameworks, anti-patterns, vocabulary, signature moves. Agents compose [lens + brand DNA + use-case] into ready-to-use prompts. New lenses can be proposed by humans or auto-proposed by upstream skills (e.g., when a trend scraper finds a recurring creator pattern)."
---

# persona-lens

> The quantitative-to-qualitative layer. Decompose creators / brands / playbooks into structured patterns, then **apply** / **fuse** / **digest** to extract first-principles.

## What a lens is

A **lens** is a structured decomposition of a person, brand, or playbook into queryable fields. Example structure for a thought-leader lens:

```yaml
slug: steve-jobs
bucket: founders
patterns:
  signature_moves: ["one-more-thing reveal", "less but better", "demos > slides"]
  pillars: ["focus", "simplicity", "vertical integration"]
  frameworks: ["computers as bicycles for the mind", "skate to where the puck is going"]
  anti_patterns: ["committee design", "speeds-and-feeds marketing"]
  vocabulary: ["insanely great", "magical", "delight"]
  voice: "calm conviction, demos > claims, second-person ('you')"
promotion_status: active
proposed_by: user:default
```

Example structure for a DTC-playbook lens:

```yaml
slug: huel-funnel
bucket: dtc-playbook
patterns:
  category: meal-replacement
  funnel_stages: ["TOFU: science-of-nutrition video ads", "MOFU: subscribe-and-save offer", "BOFU: shaker-bottle gift", "retention: macro tracker community"]
  conversion_tactics: ["limited-time bundle", "free shaker on first order", "Forbes/Times badges above the fold"]
  email_subjects: ["Your bottle, your way", "27g protein in 90 seconds"]
  takeaway_one_liner: "Science authority + frictionless first-bottle = sticky retention via community."
```

## Safety: mutating verbs default to dry-run

`add` / `propose` / `promote` / `deprecate` / `fuse` / `digest` all print what they WOULD do unless you pass `--live`. Read-only verbs (`list`, `--help`, `--selftest`) fire normally.

## The verbs

```bash
# Add a lens (immediate active)
bash scripts/persona-lens.sh add steve-jobs --bucket founders --register founder-confident --live

# Propose a lens (agent path — lands as 'candidate', awaits promote)
bash scripts/persona-lens.sh propose fayyaz-ahmed --by agent:scout \
  --bucket emerging --evidence "https://youtube.com/..." --register casual --live

# Promote a candidate → active
bash scripts/persona-lens.sh promote fayyaz-ahmed --live

# Fuse two lenses into a hybrid (status=candidate)
bash scripts/persona-lens.sh fuse steve-jobs rick-rubin --live

# Digest a bucket — extract the shared first-principles (底层逻辑) via an LLM call
bash scripts/persona-lens.sh digest --bucket founders --live

# List
bash scripts/persona-lens.sh list                              # table
bash scripts/persona-lens.sh list --bucket founders --status active --format json

# Deprecate
bash scripts/persona-lens.sh deprecate stale-slug --live
```

## Apply a lens to a creative brief

`lens-apply.sh` composes a prompt from three pieces: the lens decomposition, an optional brand DNA file, and a use-case (manifesto / ad-headline / email-flow / etc.).

```bash
# With explicit brand-dna path (most portable)
bash scripts/lens-apply.sh \
  --lens steve-jobs \
  --brand-dna /path/to/your-brand/BRAND-DNA.md \
  --use-case manifesto \
  --user-input "We're launching a new pour-over kettle."

# With brand slug + brands-dir convention
export PERSONA_LENS_BRANDS_DIR=$HOME/.persona-lens/brands   # or your path
bash scripts/lens-apply.sh --lens hormozi --brand my-brand --use-case ad-headline
```

If neither `--brand-dna` nor `--brand` is provided, the composition uses only `[lens + use-case + user-input]` — still useful.

Output is JSON with `composed_prompt` + metadata (`lens_id`, `brand_dna_path`, `composition_token_count`, `gate_warnings`).

## Auto-router: brand → best playbook

`brand-to-playbook.sh` picks the highest-ranked DTC-playbook lens for a brand by matching the brand's detected category to the lenses' categories, body richness, and use-count.

```bash
bash scripts/brand-to-playbook.sh \
  --brand my-brand \
  --use-case ad-headline \
  --auto-apply

# or with explicit DNA path
bash scripts/brand-to-playbook.sh --brand-dna /path/to/BRAND-DNA.md --with-trial
```

Modes: `--auto-apply` (fire top match), `--with-trial` (apply top-N in parallel), or no flag (print ranked list).

## Storage (all skill-local by default)

| Item | Default path | Override env var |
|---|---|---|
| Registry SQLite DB | `<skill>/data/persona-lens.db` | `LENSES_DB_PATH` |
| Lens markdown bodies | `<skill>/patterns/lenses/` | `LENSES_DIR` |
| Wiki digests | `<skill>/wiki/` | `LENSES_WIKI_DIR` |
| Decomposition sidecars | `<skill>/intel/` | `LENSES_INTEL_DIR` |
| Event logs | `<skill>/logs/` | `LENSES_LOG_DIR` |
| 30-field schema | `<skill>/schemas/lens-30field.json` | `PERSONA_LENS_SCHEMA_PATH` |
| Brand DNA directory | `$HOME/.persona-lens/brands/` | `PERSONA_LENS_BRANDS_DIR` |
| Optional policy gate | (none — skipped if unset) | `MEMPALACE_POLICY_SH` |

All paths default to skill-local so the skill works standalone on clone. Override via env vars if you want to share a registry across multiple skill clones (e.g., shared `LENSES_DB_PATH` for an org).

## Decomposer (build lenses from sources)

`lens-decomposer.sh` takes a URL or a transcript and asks an LLM to decompose it into the schema in `schemas/lens-30field.json`.

```bash
# Decompose from YouTube (uses yt-dlp auto-subs)
bash scripts/lens-decomposer.sh \
  --lens hormozi \
  --url "https://www.youtube.com/watch?v=..." \
  --live

# Or from a local transcript
bash scripts/lens-decomposer.sh --lens steve-jobs --transcript /path/to/text.txt --live

# Bulk via CSV (url,lens per row)
bash scripts/lens-decomposer.sh --bulk-csv urls.csv --max-cost 1.00 --live
```

Without `--live`, decomposer runs in dry-run mode (transcript is fetched but no LLM call is made).

## Fusion & first-principles digest

The non-obvious primitive: once you have a bucket of 20+ lenses, you can **digest** them to extract their shared first-principles.

```bash
bash scripts/persona-lens.sh digest --bucket founders --live
# Returns a JSON:
#   shared_principles: [...]
#   meta_template: "..."
#   candidate_seed_creators: [...]
```

This is how you go quantitative → qualitative — 20 decompositions → 1 distilled meta-pattern.

## LLM dependency

Two verbs touch an LLM (`lens-decomposer.sh`, `persona-lens.sh digest`). Configure via env:

```bash
export PERSONA_LENS_LLM_API_KEY=$YOUR_KEY     # or set GEMINI_API_KEY
export PERSONA_LENS_LLM_MODEL=gemini-2.5-flash # default
```

All other verbs (`add`, `propose`, `promote`, `deprecate`, `fuse`, `list`, `apply`, `brand-to-playbook`) run locally with no LLM call.

The reference provider is Google Gemini (Generative Language API). The code path is a single `curl` against `https://generativelanguage.googleapis.com/v1beta/models/<model>:generateContent`. Swap providers by editing the two `curl` blocks in `persona-lens.sh::cmd_digest` and `lens-decomposer.sh::decompose_via_llm`.

## Testing

```bash
bash scripts/persona-lens.sh --selftest      # add/list/fuse/deprecate against a temp DB
bash scripts/lens-apply.sh --selftest        # compose against a seeded sample lens
bash scripts/brand-to-playbook.sh --selftest # rank against a seeded sample brand
bash scripts/lens-decomposer.sh --selftest   # dry-run transcript decomposition (no LLM call)
bash scripts/lens-wiki-digest.sh --selftest  # generate wiki index against seeded lenses
bash smokes/smoke.sh                         # invocability + syntax check
```

All selftests use a per-invocation `mktemp -d` and clean up after themselves. They do NOT touch the default skill-local paths.

## License

MIT — see LICENSE.txt.

## Example brief

See `examples/brief-launch-manifesto.md` for a sample brief + composed output.

## Versioning

- `0.1.0` (2026-05-03) — registry + 4 verbs + decomposer + lens-apply.
- `0.2.0` (2026-05-03) — dynamic registry (no more hardcoded lists), agent-propose, fusion, digest.
- `0.3.0` (2026-05-04) — brand-to-playbook auto-router + DTC-playbook bucket.
- `0.4.0` (2026-05-12) — standalone refactor: self-contained SQLite, full env-var configurability, `--selftest` per script, ships with default 30-field schema.
