# Artifact Reproducibility Pattern (v3.3.5+)

## Why this exists

ARS produces research artifacts — draft papers, literature reviews, review reports. A year
from now, you may want to reproduce one. Today's Material Passport (Schema 9) captures WHO
produced the artifact and WHEN, but not WITH WHAT. Which LLM? Which ARS version? Which
skill files? Which session materials?

The `repro_lock` sub-block fills that gap.

When the Anthropic automated-w2s-researcher paper (2026) claimed "2 researchers × 7 days
vs 9 agents × 5 days," readers had no way to audit the conditions. This pattern ensures
that ARS-produced artifacts carry their configuration on record — not as a replay mechanism,
but as an honest documentation trail.

## What this pattern IS NOT (read this first)

This is non-negotiable. Every future user MUST read this section before assuming the lock
guarantees anything it does not.

1. **LLM outputs are not byte-reproducible even at temperature 0.** Model providers update
   weights without changing the model id. `model.weight_stable: false` acknowledges this
   explicitly. `model.id` is an identifier, not a weight hash.

2. **Live external API queries are recorded as protocol versions, not snapshots.** The S2
   API changes daily. A paper citing DOI 10.1000/x today may return different metadata
   tomorrow. `s2_api_protocol_version` records which VERSION of our query logic ran, not
   a snapshot of the response.

3. **Mid-skill prompt mutations are not captured.** `prompts.hash_timing: "skill-load"` is
   a declaration: hashes are taken when the skill loads, not per agent call. Late injection
   of user-provided reference files, conditional branches, and dynamic prompt modifications
   are NOT reflected in the hash. This is a known imprecision.

4. **`stochasticity_declaration` is required, not optional.** Omitting it makes the lock
   dishonest by implication. Every generated passport includes the declaration verbatim.

If you want deterministic replay, you are reading the wrong pattern. This pattern gives
you CONFIGURATION DOCUMENTATION sufficient to INVESTIGATE divergence — not to PREVENT it.

## The block at a glance

```yaml
repro_lock:
  schema_version: "1.0"                    # lock schema version
  stochasticity_declaration: "LLM outputs are not byte-reproducible. This lockfile documents configuration, not a deterministic replay guarantee."
  ars_version: "<suite-version-at-run-time>"   # e.g. "3.11.1" — the suite version when this run executed

  model:
    family: claude                          # provider family
    id: "<model-id-at-run-time>"           # model identifier at run time, e.g. the inherited Claude Code session model (not weight hash)
    weight_stable: false                    # always false until signed attestation exists

  prompts:
    hash_timing: skill-load                 # when hashes were taken
    skill_md_hash: "sha256:..."            # hash of the skill SKILL.md file
    agents_bundle_hash: "sha256:..."       # hash of agent prompt bundle

  materials:
    list_hash: "sha256:..."                # hash of [{filename, sha256}, ...] manifest
    count: 8                               # number of session materials

  external_protocols:
    s2_api_protocol_version: "<s2-protocol-version-at-run-time>"   # the S2 query protocol version that ran
    s2_snapshot_available: false           # whether a response cache exists

  cross_model:
    enabled: false                         # whether cross-model verification ran
    secondary_model_id: null               # secondary model id if enabled
```

The block lives as an optional child of the Material Passport (Schema 9 in
`shared/handoff_schemas.md`). A missing key fails the lint. A null value passes with a
warning. A populated block with all required sub-fields passes silently.

## Field-by-field rationale

### schema_version

`"1.0"` currently supported. Schema evolution policy: breaking changes bump major,
additions bump minor. Old readers fail loudly on unknown versions — `check_repro_lock.py`
will exit 1 if it encounters an unrecognized version, forcing the user to upgrade their
tooling or audit the change manually.

### ars_version

Suite version from CHANGELOG. This couples the prompt hashes to the release: changing
`ars_version` will change the bundle hash even if individual prompt files didn't change.
That coupling is intentional — version boundaries mark coordinated changes.

### model.weight_stable

Currently always `false`. Reserved for a future world where a provider guarantees weight
stability with a signed attestation. Not today. If you see `true`, treat it as suspicious
until a signed attestation mechanism exists.

### prompts.hash_timing

Fixed at `"skill-load"` in v1.0. A future `"per-call"` variant would require runtime
instrumentation not present today. The spec is left open for future work. For now, the
hash captures the state of files at skill initialization, not at every agent invocation.

### materials.list_hash

Hash of a sorted manifest: `[{filename, sha256}, ...]` sorted by filename. If the user
edits a session material between runs, the hash changes — which is the correct behavior.
An identical hash across two runs means the input materials were identical; different
hashes mean inputs diverged.

### external_protocols.s2_snapshot_available

Almost always `false` today. If a future version of the pipeline caches S2 responses per
run and stores them alongside the passport, this flag flips to `true` and the snapshot path
appears in the passport. Until that exists, S2 responses are live queries and are not
reproducible.

## How it composes with existing infrastructure

- Material Passport (Schema 9) is the PARENT document. `repro_lock` is an OPTIONAL CHILD
  field. A passport without `repro_lock` fails the v3.3.5+ lint; a passport with
  `repro_lock: null` passes with a warning (explicit opt-out).
- Existing passports with `repro_lock` absent fail the new lint. Existing passports with
  `repro_lock: null` pass with a warning. Populated blocks pass silently.
- The integrity gate (Stage 2.5, Stage 4.5 in the academic pipeline) does NOT read
  `repro_lock`. The lock is for post-hoc reproducibility investigation, not runtime
  validation. Adding it does not change pipeline behavior.
- `check_repro_lock.py` can be run standalone on any passport file. It is not wired into
  the CI lint suite by default — it validates on-demand against specific passport files.

## Red flags when reading a populated repro_lock

- `model.weight_stable: true` — this value is not implemented yet; if you see it, the
  passport author is claiming something the infrastructure cannot verify. Treat as
  suspicious until a signed attestation mechanism exists.
- `prompts.hash_timing` anything other than `"skill-load"` — this is an unknown variant
  that the current tooling does not understand. The lint will not flag it as invalid, but
  the semantics are undefined.
- Empty or stub hashes (`"sha256:"` prefix with no content, or a short placeholder string
  like `"sha256:abc123"`) — the generator was broken or the author filled in a placeholder.
  Hashes should be 64-character hex strings for SHA-256.
- `stochasticity_declaration` modified from the verbatim required string — the author is
  signalling they believe the lock is stronger than it is. Read the entire passport twice
  before trusting any claims about reproducibility.

## How to generate a lock (for agent authors)

At skill-load time, compute `skill_md_hash` over the SKILL.md content and
`agents_bundle_hash` over the concatenated agent prompts (canonical ordering). Build the
materials manifest by listing session files with their SHA-256 digests, sort by filename,
then hash the JSON serialization. Write the block to the passport before handing off to
downstream stages. The `stochasticity_declaration` must be included verbatim — do not
paraphrase or abbreviate it.

## Honesty red line (restate)

This pattern enables HONEST DOCUMENTATION. It does not enable REPLAY. Every field has a
reason and a limitation. Users who treat the lock as a replay guarantee will be burned.
Authors who publish passports without `stochasticity_declaration` are failing their readers.
The locked configuration tells you what ran; it cannot tell you what would run again.

The distinction matters: documentation lets a third party investigate what happened and
ask whether divergence is expected or alarming. Replay would require weight-frozen models,
deterministic schedulers, and cached external data — none of which ARS controls today.

## Future evolution

- v1.1: add `cache_snapshot_available: true` support once the pipeline caches S2 responses.
  The snapshot path would appear as a sibling field in `external_protocols`.
- v2.0: if weight-signed attestations exist, `model.weight_stable: true` becomes meaningful.
  Until then the field is reserved.
- Never: byte-level replay guarantees. LLMs don't work like that; no schema version will
  change that fact.
