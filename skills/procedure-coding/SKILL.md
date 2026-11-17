---
license: Provided under Anthropic's Terms of Service (not the Apache-2.0 LICENSE.txt used by most skills in this repo) — see NOTICE.md
source: https://github.com/anthropics/healthcare/tree/main/plugins/healthcare/skills/procedure-coding
name: procedure-coding
description: Assign CPT and HCPCS Level II procedure codes from clinical documentation the way a professional coder builds the claim. Use when users say "code this encounter for procedures", "what CPT codes apply", "assign HCPCS codes", "code this op note", or when turning visit notes or operative reports into claim-ready procedure codes.
---

# Procedure Coding from Encounter Documentation

Turn one encounter's clinical documentation into the procedure codes a professional coder would submit on the claim: CPT (five digits, or four digits + F for Category II tracking codes) for physician services, procedures, and quality measures, plus HCPCS Level II (letter + four digits) for supplies, devices, and non-physician services CPT does not cover.

## Step 1 — Abstract every billable service from the note

Read the documentation and list each distinct billable service performed at this encounter. Work by category:

- **Evaluation and management** — the visit itself: office, emergency, observation, inpatient, consultation. One E/M code per encounter unless a separately identifiable service is documented. When the visit is for ongoing management of a single serious or complex chronic condition, the complexity add-on may apply alongside the office E/M code.
- **Ancillary services that ride alongside the visit** — a blood draw for any lab is a separately billable venipuncture; each lab test ordered with a result in the note bills its own code; an ECG or pulse-ox performed in the visit is its own code; an injection, infusion, or IV push administered during the visit codes the administration plus an add-on for each additional sequential push or hour.
- **Procedures and surgery** — anything with an incision, injection, scope, repair, or manipulation. Abstract from the procedure note, not the plan.
- **Laboratory and pathology** — each ordered test that has a result in the note. Panels (CBC, BMP, CMP) bill as the panel code, not the components.
- **Imaging** — each study by modality and body part, with the view/contrast detail documented.
- **Medicine services** — vaccinations administered, infusions, therapeutic injections, ECGs, pulmonary function, physical therapy.

Leave off the list: services planned but not performed, results referenced from a prior date, and items already bundled into a procedure's global package.

## HCPCS Level II — what to look for and what to leave off

HCPCS Level II codes (one letter + four digits) cover items CPT does not. Check the documentation for these specifically:

- **Hospital observation hours** — when the note shows the patient was placed in or remained in observation status, code the per-hour observation service (and the direct-referral code when the patient was placed in observation without a preceding ED visit).
- **Devices and implants used during a facility procedure (C-codes)** — for any catheterization, endoscopy, interventional, or implant procedure, read the operative/procedure narrative and the supply or implant log for each single-use device the operator names: guide wire, introducer or sheath, diagnostic or guiding catheter, lead, stent, closure or embolization device, balloon. Operative prose often names these in passing ("wire advanced," "sheath placed," "device deployed") rather than in a discrete list — abstract each one. Each device the procedure consumed codes separately under hospital outpatient rules.
- **Drugs administered in the facility (C-codes)** — certain injectable drugs given during a hospital outpatient encounter carry their own pass-through code. Scan the medication-administration record or nursing notes for IV-push or infusion drugs given during the stay and match by drug name.
- **Specimen collection performed by facility staff** — a documented swab or draw billed by the facility separately from the lab test.
- **Supplies dispensed** (A-codes) — sterile saline, dressings, trays, ostomy supplies, when the note or supply record names the specific item.
- **High-throughput infectious-disease lab tests** (U-codes) — when the lab order or result names the specific assay platform.
- **Medicare preventive and screening services** (G0-codes) — annual wellness visit, advance-care-planning, depression or alcohol screening, diabetes prevention. Code only when the note documents the specific service was performed at this visit, not when the topic appears in history.

**Do not output quality-reporting G-codes (G8-/G9- range) or non-covered-item codes.** These report participation in a quality program or a coverage determination; whether they belong on the claim depends on the practice's program enrollment and the payer, not on the clinical documentation. A data point appearing in the note (BMI in vitals, medication list reviewed, tobacco status in social history) is not by itself a reason to report the corresponding quality code.

## CPT Category II (####F) — same rule as quality G-codes

Category II tracking codes are reported when the encounter is part of a quality-reporting workflow, not whenever the data point happens to appear in routine vitals or history. Output a ####F code only when the note shows the measure was deliberately captured for reporting: a quality-measure or health-maintenance section, measure-specific attestation language, or a structured screening result.

## Step 2 — Find each code with the lookup tools

For every item on your abstracted list, search before you commit.

**HCPCS Level II (letter + four digits):** use `search_codes` for the supply, device, drug, or service name, passing the encounter date as `as_of`. Confirm with `validate_code` and the same `as_of`.

**CPT (five-digit and ####F):** if a CPT lookup connector is available (`cpt_search_codes`), use it with the service in plain words taken from the note and confirm with `cpt_lookup_code`. If no CPT connector is available, propose CPT codes from your knowledge of the current code set and state that they are pending verification against the user's licensed CPT reference — CPT descriptors are AMA-licensed and not bundled with this skill.

One or two searches per item is sufficient. If the right code is not in the first results, refine the query once with more specific wording from the note; then commit or move on. Do not loop on the same item.

## Step 3 — Output

After tool calls, output only the codes that belong on the claim, one per line, no other text. List each code once. Do not output J#### or Q#### codes. If a service you abstracted has no matching code in the lookup results and you cannot confidently propose one, omit it rather than guessing.
