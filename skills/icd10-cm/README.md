# ICD-10-CM Coding Skill

Extract billable ICD-10-CM diagnosis codes from clinical notes the way a professional coder builds a claim.

Part of the Claude for Healthcare plugin, whose bundled ICD-10 Codes connector provides the skill's lookup tools out of the box. Further code-system skills (procedure coding, drug/supply coding) and a coding-audit workflow slot in alongside it as they're built.

## What it does

Given a clinical note (visit note, encounter summary, discharge note), the skill produces the diagnosis codes a coder would submit on the claim for that encounter:

1. **Claim selection** — decides which conditions belong on the claim (reason for visit, conditions managed this visit) and which stay off (history mentions, uncertain diagnoses, symptoms already explained by a coded diagnosis).
2. **Documented specificity** — codes exactly what the clinician documented: unspecified when the note doesn't subtype, specific when it does, never inferring complications from labs or imaging alone.
3. **Verified lookup** — every code is confirmed against a current ICD-10-CM source rather than recalled from memory, so post-2022 code-set changes (e.g. F32.A) are handled correctly.

## Lookup

All code lookup goes through the bundled ICD-10 Codes connector (`search_codes`, `lookup_code`, `validate_code`) — no shell or network access is requested by the skill itself. If the connector is unavailable, the skill stops and asks for it rather than coding from memory: unverified recall is the main source of stale-code-set errors.

## Scope

Written for and validated on **outpatient encounter coding** (primary care, ambulatory follow-ups, minor injury visits). Inpatient-specific conventions (POA indicators, DRG considerations) and specialty regimes with heavy 7th-character logic (poisonings/adverse effects, obstetrics) are not specifically covered.

This skill assists coding workflows; it does not replace certified coder review. Final claim responsibility remains with the billing provider.
