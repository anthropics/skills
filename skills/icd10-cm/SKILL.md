---
license: Provided under Anthropic's Terms of Service (not the Apache-2.0 LICENSE.txt used by most skills in this repo) — see NOTICE.md
source: https://github.com/anthropics/healthcare/tree/main/plugins/healthcare/skills/icd10-cm
name: icd10-cm-skill
description: Extract billable ICD-10-CM diagnosis codes from a clinical note the way a professional coder builds the claim. Use when users say "code this encounter", "assign ICD-10 codes", "what diagnosis codes apply", "code this chart", or when turning clinical documentation into claim-ready diagnosis codes.
---

# ICD-10-CM Coding from Clinical Notes

Turn a clinical note into the diagnosis codes a professional coder would submit on the claim for that encounter. This happens in two distinct steps: first decide *which* conditions belong on the claim, then find the *exact* code for each. Both steps cause errors: coders miss claims by listing the wrong conditions, and by coding the right condition at the wrong specificity.

## Step 1: Decide what belongs on the claim

A claim reflects the encounter, not the patient's chart. Per the ICD-10-CM Official Guidelines for outpatient coding:

**Code, in this order:**
1. The reason for the visit (first-listed diagnosis). When the visit itself is for aftercare, screening, or follow-up, the Z-code IS the first-listed diagnosis — e.g. orthopedic aftercare/hardware removal (Z47.x), suture removal (Z48.02), a scheduled wellness exam (Z00.0x).
2. Conditions evaluated, managed, or treated at this visit — a medication refill or "stable, continue current plan" counts as managed.
3. Chronic comorbidities, but only if they were addressed or changed medical decision-making this visit.

**Symptoms:** when the patient came in FOR a symptom and the visit ends with no established diagnosis, that symptom is the first-listed diagnosis — code it (low back pain M54.5x, joint pain M25.5xx). That is the only time a symptom is coded. A symptom that accompanies a coded diagnosis (headache with a coded neck injury, dizziness with coded vertigo, fatigue with coded anemia) is part of that diagnosis and never coded separately.

**Leave off the claim:**
- Uncertain diagnoses — "probable", "suspected", "rule out". In outpatient coding these are never coded; code the presenting symptom instead.
- Conditions mentioned only as history and not treated today.
- Wellness-exam codes (Z00.0x) on a problem-focused visit. They belong only when the encounter is an actual scheduled physical.
- Status, lifestyle, and counseling codes — nicotine dependence (F17.x), alcohol use (F10.x), long-term medication (Z79.x), device/stent status (Z95.x), counseling (Z71.x) — unless that item is a substantial focus of the visit, not a passing mention or routine social-history line.
- External-cause codes (V00–Y99, how an injury happened): outpatient claims rarely carry them and most payers don't require them — the injury code itself carries the claim. Include them only when the setting or payer specifically requires external-cause reporting.

A correctly coded outpatient encounter is short — usually 1 to 4 codes. If your draft list is longer, you are coding the problem list rather than the encounter; cut anything that wasn't actually evaluated, managed, or treated this visit.

## Step 2: Code at the documented specificity

This is where most miscoding happens. Two rules:

**Don't hedge on a diagnosis.** Never list sibling codes, candidate alternatives, or a category plus its children for the *same* diagnosis — commit to the single code the documentation supports for each. If you are torn between two codes for one diagnosis, the documentation is undetailed and the unspecified code wins.

**Code exactly what the note documents — never above it, never below it.**
- **Default to unspecified when the note doesn't subtype.** "Asthma" with no severity → J45.909. "Psoriatic arthritis" with no subtype → L40.50. "Type 2 diabetes" with no complication linked in the note → E11.9. "Hepatitis C" without documented chronicity → B19.20. Unspecified (.9, .50, .909) is the *correct* code for an undetailed note — it is not a fallback or a failure.
- **Do not infer** chronicity, severity grades, laterality, episode type, or diabetes-complication links that the note doesn't state. An ulcer coded with a severity character (L97.x1x "limited to breakdown of skin") requires the note to actually stage the depth; otherwise use unspecified severity (L97.x19).
- **A complication or subtype must be linked by the clinician, not assembled from data.** Lab values, vitals, and imaging findings in the note do not by themselves make a complication codable — an elevated A1c does not establish "T2DM with hyperglycemia," and an echo finding does not establish the heart-failure subtype, unless the clinician's own assessment states it. Code from the assessment wording; if the assessment names the condition without the complication, code it unspecified.
- **Add-on codes accompany their base code, never replace it.** Resistant hypertension I1A.0 is assigned in addition to I10; if you use an add-on, the base code stays on the claim.
- **"Other specified" (.8, .59) is not "unspecified."** Use it only when the note names a specific subtype that has no code of its own. No subtype documented → unspecified, not "other."
- **Never output a bare category.** J45, F32, E11, N20 alone are not billable codes. Every code must be carried to its full billable length.
- **Use the documentation when it IS specific.** "Acute on chronic systolic heart failure" → I50.23, not I50.9. Under-coding documented detail loses exactly as much as over-inferring.

## Step 3: Find the exact code via the ICD-10 connector

Look up every diagnosis with the ICD-10 Codes connector's tools — **including diagnoses you're sure you know.** Code sets change every October and your memory of common codes can be stale; for example, "depression, unspecified" has been F32.A (not F32.9) since 2022. The connector has the current set; trust it over recall.

- Use `search_codes` with `code_type="diagnosis"`, building the query from the note's own wording plus the specificity decision from Step 2 — if you decided "unspecified," put "unspecified" in the search terms.
- Take the first result whose description matches the note's wording. If the first result's type, laterality, or complication status contradicts the note (e.g. "Type 1" when the note says "type 2"), it is not a match — move to the next result or refine the query once. Don't page through more than the top few results.
- Confirm the chosen code with `lookup_code` or `validate_code` — every code on the claim must be valid and billable.
- The connector returns complete codes, including 7th characters (A/D/S) and X placeholders for injury codes. Copy the code exactly as the connector returns it — if it includes a dot, keep the dot; if not, don't add one. Do not reformat, strip, or extend what the connector gave you.

**If the connector's tools are not available, stop.** Tell the user the ICD-10 Codes connector needs to be installed or enabled, and do not produce codes from memory — codes recalled without verification are exactly where stale-code-set errors come from.

## Working style

Work through Steps 1–3 using tool calls only. Don't write explanatory text between searches — no running commentary, no candidate-by-candidate analysis in prose. Your reply is consumed by a claims pipeline that reads every code string in it, so the only prose you produce is the final answer itself, and the only code strings in it are the claim.

## Step 4: Final check

Walk your draft list once before answering. For each code ask:
1. Does the note show this condition was evaluated, managed, or treated *at this visit*?
2. Is the specificity exactly what the note documents — unspecified if undetailed, detailed if documented?
3. Is this the ONLY code on the list for this diagnosis, at full billable length, taken from a lookup result, dots removed?

Keep the code only if all three hold. If two codes describe the same diagnosis, delete one before answering.

## Answer format

End with the codes on their own labeled lines so the first-listed diagnosis is unambiguous:

```
First-listed: E11.65
Secondary: I10, Z79.4
```

Codes appear exactly as returned by the connector — dots included. Any reformatting for a specific claims system happens downstream, not here.
