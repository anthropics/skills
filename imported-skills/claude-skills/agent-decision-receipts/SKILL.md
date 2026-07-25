---
name: "agent-decision-receipts"
description: "Mint a tamper-evident, post-quantum-signed receipt for a consequential agent action (deploy, delete, pay, grant-access, model decision) so it can be verified later from the certificate alone. Use when an autonomous agent takes a side-effecting action that may need to be proven later, or when satisfying EU AI Act Article 12 record-keeping. Three decisions: whether an action needs a receipt, minting it, verifying it. Signing is delegated to the open-source OpenAgentOntology package. Not after-the-fact log analysis; not a hosted notary; not a legal opinion."
---

# Agent Decision Receipts

## Overview

A log says an action happened. A **receipt is tamper-evident**: it records who, what, and under which policy, and it is signed, so any later edit breaks the signature. This skill mints one for a consequential agent action and verifies it later from the certificate alone: no database, no network, no trusting the issuer.

The crypto is not in this skill. It is the open-source **OpenAgentOntology** receipt primitive (Apache-2.0), which signs every receipt with Ed25519 **and** the post-quantum legs ML-DSA-65 (FIPS 204) + SLH-DSA (FIPS 205) when the post-quantum backend is installed. This skill is the decision layer: when to mint, what to put in, how to verify. One install, no per-skill crypto.

**Three decisions, nothing else:**

1. **Does this action need a receipt?** — side-effecting + consequential + later-provable = yes.
2. **Mint the receipt** — build the action manifest, sign it with the OAO primitive.
3. **Verify it** — recompute the hash, check each signature leg, from the cert alone.

This skill is **NOT log analysis.** Logs describe what happened and can be silently edited. A receipt is minted before/at execution and breaks if edited. Use logs for debugging; use receipts for evidence.

This skill is **NOT a hosted notary.** It mints a LOCAL, self-signed receipt anyone can verify offline. Cross-organization verification (one org proving to another) is a separate hosted service, out of scope here.

This skill is **NOT a legal opinion.** It produces evidence shaped to support FRE 902(13)/(14)-style certification and EU AI Act Article 12 record-keeping. Whether a given receipt is admitted is a question for counsel.

## Quick Start

```bash
# Install the open-source receipt primitive (Apache-2.0). Add [pq] for the post-quantum legs.
pip install "openagentontology[pq]"

# 1. Build + validate an action manifest (stdlib only, no crypto, no network)
python scripts/build_action_manifest.py --agent my-deploy-agent --operation deploy \
    --target prod/api --policy "EU AI Act Art 12" --out action.json

# 2. Mint the receipt over it (Ed25519 + post-quantum legs)
python -c "import json,openagentontology.receipt as r; \
  print(json.dumps(r.mint_receipt(json.load(open('action.json')), decision='ACTION_GOVERNED')))" > receipt.json

# 3. Verify from the cert alone (no DB, no network)
python -c "import json,openagentontology.receipt as r; \
  print(r.verify_receipt(json.load(open('receipt.json'))))"
# -> {'ok': True, 'sig_ok': True, ... 'reason': 'verified from the cert alone via: ed25519, ml_dsa, slh_dsa'}
```

> **Dependency note.** This skill delegates the signing to `openagentontology` (Apache-2.0, opt-in `pip install`). The script shipped here is stdlib-only and adds no repo dependency; the package is installed by the operator (BYO-library pattern). If it is not installed, the build step still works — only minting/verifying require it.

## Core Workflow

The three decisions below are the skill: decide whether to receipt, mint, then verify.

## Decision 1: Does this action need a receipt?

Mint a receipt when the action is **all three** of:

| Test | Mint if... |
|------|-----------|
| Side-effecting | it writes, sends, deploys, deletes, pays, grants access, or changes external state |
| Consequential | a wrong call costs money, breaks compliance, or harms a person |
| Later-provable | someone (auditor, insurer, regulator, court, counterparty) may ask "what did the agent do and why?" |

Read-only, reversible, trivial actions do **not** need a receipt. Receipt everything and the signal drowns; receipt nothing and the one call that mattered cannot be proven.

High-signal triggers (mint by default): `deploy`, `delete`, `pay`/`wire`/`refund`, `grant_access`, `export`/`egress`, `approve`/`deny` a claim, any model decision that affects a person under a high-risk AI system.

## Decision 2: Mint the receipt

The action manifest is any ASCII-safe dict describing what the agent did. Four keys are **required** — `build_action_manifest.py` rejects the manifest (exit 2) if any is missing. Two more are added automatically:

| Key | Required? | What it carries |
|-----|-----------|-----------------|
| `agent_id` | **required** | the acting agent |
| `operation` | **required** | the verb (deploy / delete / pay / decide / ...) |
| `target` | **required** | what it acted on |
| `policy` | **required** | the rule that governs it (e.g. "EU AI Act Art 12", "internal change-control") |
| `inputs_hash` | auto-added | a hash of `--inputs`, so the full payload need not be stored in the clear (defaults to the hash of empty when `--inputs` is omitted) |
| `decision_label` | auto-added | the receipt decision label (defaults to `ACTION_GOVERNED`) |

`mint_receipt(manifest, decision=...)` hashes the full manifest into the receipt evidence, signs the canonical body, and returns a receipt that carries: `evidence_hash`, `signature_b64` (Ed25519), and — when `[pq]` is installed — `ml_dsa_signature_b64` + `slh_dsa_signature_b64`. Each leg signs the same bytes; any one verifying proves authenticity.

> See [references/receipt-fields.md](references/receipt-fields.md) for the full receipt schema and the post-quantum rationale.

## Decision 3: Verify it

`verify_receipt(receipt)` recomputes `sha256(canonical(evidence))`, compares it to `evidence_hash`, then checks every signature leg it has a backend for. It returns `{ok, hash_ok, sig_ok, legs, reason}`. A single edited byte anywhere in the action breaks `hash_ok`; a forged signature breaks the leg. Verification needs only the receipt — no call back to the issuer.

This is the property that makes it evidence: a reviewer who distrusts the issuer can still confirm the receipt is intact and authentic, entirely offline.

## Anti-Patterns

- **Receipt the log, not the decision.** Minting a receipt over a log line written after the fact proves nothing. Mint at the point of action, over the action.
- **Storing the signing key next to the receipts.** If the key is compromised, signatures mean nothing. Treat the key like any signing secret; never commit it.
- **Ed25519-only when the post-quantum legs are available.** A receipt is long-lived evidence. Sign it once with the post-quantum legs (ML-DSA-65 + SLH-DSA) so it stays verifiable if a future quantum computer could break Ed25519. Install `[pq]`.
- **Putting raw secrets or PII in the manifest.** The manifest is hashed into evidence and is recoverable from the receipt. Carry hashes (`inputs_hash`), not the cleartext.
- **Calling it "admissible."** It is evidence shaped to *support* FRE 902(13)/(14)-style certification. Admissibility is a court's decision, not the tool's claim.
- **Faking a signature when crypto is missing.** The primitive emits an explicit `unsigned` flag instead. Never present an unsigned receipt as signed.

## Cross-References

- `ra-qm-team/skills/eu-ai-act-specialist/` — decide the AI system's risk tier and Article 12 obligations; this skill mints the per-action record those obligations require.
- `ra-qm-team/skills/iso42001-specialist/` — the AI management-system controls; receipts are the per-decision evidence those controls call for.
- OpenAgentOntology (Apache-2.0): the open receipt primitive this skill drives — `pip install "openagentontology[pq]"`.
