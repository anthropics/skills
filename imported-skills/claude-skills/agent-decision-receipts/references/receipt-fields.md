# Receipt fields + the post-quantum rationale

Detailed reference for the `agent-decision-receipts` skill. The receipt is produced by the
OpenAgentOntology `mint_receipt` primitive (Apache-2.0); this documents what comes back and why.

## The receipt schema

A minted receipt is an ASCII-only, JSON-safe dict:

| Field | Meaning |
|-------|---------|
| `atom_id` | stable id derived from the action source + the evidence-hash prefix |
| `type` | `AgentGovernanceReceipt` |
| `decision` | the verdict label passed in (e.g. `ACTION_GOVERNED`, `DEPLOY_APPROVED`) |
| `evidence_hash` | `sha256(canonical(evidence))` — the commitment to the full action manifest |
| `signed_at` | ISO-8601 timestamp (in the signed body, never in the hashed evidence) |
| `evidence` | `{summary, ontology}` — the full action manifest is under `evidence.ontology` |
| `signature_b64` | Ed25519 signature over `canonical(body)` |
| `verify_pubkey_b64` | the Ed25519 public key, so the receipt verifies offline |
| `signed` | bool — false + an explicit flag if the crypto backend is absent (never faked) |
| `ml_dsa_signature_b64` | ML-DSA-65 (FIPS 204) leg, present when `[pq]` is installed |
| `slh_dsa_signature_b64` | SLH-DSA (FIPS 205) leg, present when `[pq]` is installed |
| `signature_alg` | names every leg actually on the receipt |
| `kid` | `sha256(verify_pubkey_b64)[:32]` — 128-bit key identifier. Lets a verifier comparing two receipts answer "signed by the same key?" offline, without any registry. |

## Canonicalization (why the hash reproduces anywhere)

`canonical(obj) = json.dumps(obj, sort_keys=True, separators=(",",":"), ensure_ascii=True, allow_nan=False)`.

Because the evidence is sorted, separator-fixed, ASCII, and finite, a verifier in any language
recomputes the identical `sha256` byte-for-byte. There are no timestamps inside the hashed
evidence, so the hash is deterministic; the timestamp lives in the signed body instead.

## Verification result

`verify_receipt(receipt)` returns:

| Field | Meaning |
|-------|---------|
| `hash_ok` | recomputed `sha256(canonical(evidence))` equals `evidence_hash` |
| `legs` | per-leg status: `ok` / `fail` (tamper) / `absent` / `unverifiable` (no backend) |
| `sig_ok` | at least one signature leg verified |
| `ok` | `hash_ok` AND no leg failed AND (`sig_ok` OR the receipt is honestly unsigned) |
| `reason` | human-readable verdict |

A one-byte edit to the action breaks `hash_ok`. A forged signature flips a leg to `fail`. An
older Ed25519-only receipt still verifies; the post-quantum legs are simply `absent`.

## Why post-quantum, by default

A receipt is long-lived evidence — an insurer, a regulator, or an auditor may verify it years
after the action. A cryptographically-relevant quantum computer could forge Ed25519 signatures,
so a signature that must stay trustworthy for years needs an algorithm that resists that. The
post-quantum legs are NIST-standardized signatures designed for exactly this:

- **ML-DSA-65** (FIPS 204) — lattice-based; the size/performance default for hot paths.
- **SLH-DSA** (FIPS 205) — hash-based, stateless; smaller assumptions, good for long archival.

Each leg signs the same canonical body, so a verifier with only one backend can still prove
authenticity from whichever leg it can check. This is post-quantum *cryptography* (quantum-
resistant signatures on classical computers), not quantum computing — label it precisely.

Install both legs: `pip install "openagentontology[pq]"`.

## PQ-required verification (strict mode, recommended)

A verifier that accepts Ed25519-only receipts can be fooled by an attacker who strips the
post-quantum legs from a hybrid-signed receipt — the residual Ed25519 leg still verifies, but the
long-lived guarantee is gone. For long-lived evidence, require the post-quantum legs to be present
and valid, and only accept Ed25519-only receipts when you must verify legacy archival data:

```python
import os
import openagentontology.receipt as oao

def verify_strict(receipt, *, require_pq: bool | None = None):
    must = require_pq if require_pq is not None else (
        os.environ.get("RECEIPT_REQUIRE_PQ", "true").lower() in ("1", "true", "yes", "on"))
    out = oao.verify_receipt(receipt)
    if must and out.get("ok") and out.get("signed"):
        legs = out.get("legs", {})
        missing = [n for n in ("ml_dsa", "slh_dsa") if legs.get(n) != "ok"]
        if missing:
            out["ok"] = False
            out["reason"] = f"PQ-required: missing {missing}"
    return out
```

Default the gate to on; set it off only for legacy Ed25519-only archival receipts.
