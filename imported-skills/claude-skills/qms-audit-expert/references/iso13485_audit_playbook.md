# ISO 13485:2016 Internal Audit Playbook

This reference answers exactly one decision: **how do we conduct an ISO 13485 QMS internal audit (Clause 8.2.4) that satisfies certification body expectations and supports MDR / FDA QSR alignment?**

Pair with `scripts/audit_schedule_optimizer.py` (this skill) for cadence and with `compliance-os/scripts/audit_simulator.py` for mock-audit preparation.

## When to Use This Playbook

- Annual Clause 8.2.4 internal audit programme
- Pre-stage-1 ISO 13485 certification readiness
- Surveillance audit preparation (year 2 / year 3)
- New medical device introduction (DHF closure audit)
- Post-CAPA closure verification audit
- Bridge audit for FDA QSR / EU MDR alignment

## Key Difference from ISO 27001 Audits

ISO 13485 audits emphasize:

1. **Design controls (Clause 7.3)** — DHF/DMR completeness, design verification + validation evidence, traceability matrix
2. **Process validation (Clause 7.5.6)** — IQ/OQ/PQ for manufacturing + sterilization + cleaning processes
3. **Document control (Clause 4.2)** — strict version control + change control for all controlled documents
4. **CAPA (Clause 8.5.2)** — closed-loop with root cause analysis; "containment / correction / corrective action" distinction
5. **Post-market surveillance (Clause 8.2.1)** — vigilance reporting, customer feedback loop, trend analysis
6. **Risk management (Clause 7.1 + ISO 14971)** — risk file maintained across product lifecycle

ISO 13485 audits are **more prescriptive** than 27001 — auditors expect specific record formats, sign-offs, and traceability that 27001's risk-based approach does not require.

## The 7-Phase Audit Workflow

Same 7-phase structure as ISO 27001 (Plan → Prepare → Open → Field → Close → Report → Track), with these QMS-specific differences:

### Phase 1 Plan — Scope Selection

ISO 13485 organizes clauses by lifecycle activity. Audit fieldwork organizes by:

- **Design controls (Clause 7.3)** — DHF audit per product
- **Production & service provision (Clause 7.5)** — process validation evidence
- **Management responsibility (Clause 5)** — management review records
- **Resource management (Clause 6)** — competence + infrastructure + work environment
- **Measurement, analysis, improvement (Clause 8)** — internal audit programme + CAPA + nonconformity + statistical techniques

3-year rolling coverage: every clause audited at least once, with design + CAPA + post-market in higher rotation due to risk weight.

### Phase 4 Field — QMS-Specific Sampling

For design controls (Clause 7.3) — sample DHFs:

- Stratified by product class (Class I, IIa, IIb, III per MDR; Class I/II/III per FDA)
- For each sampled DHF, verify:
  - Design + development plan with stages + reviews defined
  - Design inputs traceability to user needs / clinical requirements
  - Design outputs verification evidence
  - Design validation evidence (clinical evaluation per MDR Annex XIV / 510(k) summary per FDA)
  - Design transfer evidence
  - Design changes controlled per Clause 7.3.9
  - DHF complete and archived

For CAPA (Clause 8.5.2) — sample CAPA records:

- Stratified by source (customer complaint, internal audit, management review, nonconformity)
- For each sampled CAPA, verify:
  - Problem statement clear + measurable
  - Root cause analysis evidence (5 Why, fishbone, Pareto, FMEA — pick the method)
  - Containment + correction + corrective action distinction documented
  - Effectiveness verification with evidence (re-test or sample post-implementation)
  - Closure approved by appropriate authority

For post-market surveillance (Clause 8.2.1) — sample:

- Customer complaint log + investigation closure
- Vigilance reports (serious incident / FSCA) submitted per applicable regulation
- Trend analysis evidence + management review input
- Post-market clinical follow-up evidence (per MDR for high-risk devices)

## Common Stage 1 / Stage 2 Findings (the patterns)

Based on practitioner reports of common ISO 13485:2016 findings:

1. **Design changes not always controlled per Clause 7.3.9** — emergency changes bypass review
2. **DHF incomplete** — design history files missing one or more required elements
3. **Process validation incomplete or stale** — IQ/OQ/PQ done at original setup, never re-validated
4. **CAPA effectiveness verification missing** — corrective action closed without evidence of effectiveness
5. **Risk management file not updated post-launch** — ISO 14971 risk file frozen at release
6. **Supplier evaluations exist but selection criteria not documented**
7. **Internal audit programme misses some clauses over 3-year cycle**
8. **Management review missing required inputs** (audit results, nonconformity status, customer feedback, etc.)
9. **Training records lack evidence of effectiveness verification**
10. **Document control: obsolete documents accessible in shared drives**
11. **Validation of software used in QMS (per Clause 4.1.6) not performed**
12. **Post-market surveillance plan exists but not executed quarterly**

## MDR 2017/745 + FDA QSR Overlap

ISO 13485 is the foundation for both EU MDR and FDA QSR compliance.

### EU MDR cross-walk

| ISO 13485 clause | MDR article / annex |
|---|---|
| 4.2 Documentation | Annex II + Annex III (technical documentation) |
| 5 Management responsibility | Article 10(1)-(9) |
| 6 Resource management | Article 10(13) |
| 7.1 Risk management | Annex I §3 + ISO 14971 |
| 7.3 Design + development | Annex II + Annex VIII (design dossier) |
| 7.4 Purchasing | Article 10(4) + Annex II |
| 7.5.6 Process validation | Annex IX §3 |
| 8.2.1 Post-market surveillance | Article 83 + Article 86 + Annex III |
| 8.5.2 CAPA | Article 87 (vigilance) + Article 89 (CAPA) |

### FDA legacy QSR (21 CFR 820, historical) cross-walk

> **⚠️ STATUS — QMSR transition (effective 2026-02-02):** FDA's QMSR final rule (89 FR 7496) amended 21 CFR Part 820 to incorporate ISO 13485:2016 by reference and removed the legacy QSR subsection structure. The 820.x numbers below **no longer exist in the CFR** — they are retained only as a familiar index for auditors mapping pre-2026 documentation. Cite the ISO 13485 clauses in current audits.

| ISO 13485 clause (current authority) | Legacy QSR section (historical, pre-2026) |
|---|---|
| 4 QMS | 820.20 (Management responsibility) + 820.5 (QMS) |
| 7.3 Design controls | 820.30 |
| 7.4 Purchasing controls | 820.50 |
| 7.5.6 Process validation | 820.75 |
| 8.2.1 Post-market | 820.198 (Complaint files) + 803 (MDR reporting — unchanged) |
| 8.5.2 CAPA | 820.100 |

FDA finalized the QMSR rule in February 2024 (89 FR 7496) incorporating ISO 13485:2016 into 21 CFR 820, substantially harmonizing US and international requirements; it took effect 2026-02-02. An ISO 13485-certified QMS now substantially satisfies 21 CFR 820, with FDA-specific overlays in retained 820.10/820.35/820.45 (labeling, complaint records) and unchanged 21 CFR 803 MDR reporting.

## Risk Management Audit (ISO 14971 Crosswalk)

Per Clause 7.1 + ISO 14971:2019, the risk management file (RMF) must be maintained for the device lifecycle. Audit should sample:

- Risk management plan exists per product
- Hazard identification covers reasonable foreseeable misuse
- Risk analysis applies probability × severity per ISO 14971
- Risk control measures applied per inherent safety → protective measures → information for safety hierarchy
- Residual risk evaluated + accepted (with rationale)
- Post-production information feeds back into RMF (concept drift equivalent for medical devices)

## CAPA Discipline — The Highest-Stakes Audit Area

CAPA is the #1 cited area in 13485 + QSR audits. Auditors look for:

1. **Containment vs correction vs corrective action distinction**
   - Containment: stop the bleeding (short-term)
   - Correction: fix the symptom (medium-term)
   - Corrective action: prevent recurrence by addressing root cause (long-term)
2. **Root cause analysis depth** — 5 Why minimum; ideally fishbone + Pareto for repeat issues
3. **Effectiveness verification** — measurable evidence the root cause is addressed; not "we updated the procedure"
4. **Time to close** — tracked + reported; aging CAPAs > 90 days are a smell
5. **Trend analysis** — repeat CAPAs across products signal systemic issue

## Cross-Framework Reuse

This ISO 13485 audit playbook supports:

- **EU MDR 745** — design dossier + technical documentation audits (see mdr-745-specialist)
- **FDA QSR (21 CFR 820)** — substantially harmonized post Feb 2026
- **ISO 14971** — risk management file audit integrated with 7.1
- **ISO 42001** for AI-enabled medical devices — A.6 lifecycle controls layer on top of 7.3 design controls

Pair with `compliance-os/references/multi_framework_audit_playbook.md` for medical-device multi-framework programs.

## When This Reference Doesn't Help

- **Specific medical device classification.** See mdr-745-specialist + fda-consultant-specialist.
- **Specific clinical evaluation.** Per MDR Annex XIV; see mdr-745-specialist references.
- **Software as medical device (SaMD).** IEC 62304 specific; see risk-management-specialist + applicable references.
- **External notified body audit.** This is the internal audit playbook; external surveillance audits follow ISO 17021.

---

**Source authorities (non-exhaustive):**

- **ISO 13485:2016** — Medical devices — Quality management systems (the standard)
- **ISO 14971:2019** — Application of risk management to medical devices
- **ISO/IEC 19011:2018** — Guidelines for auditing management systems
- **ISO 17021-1:2015** — Conformity assessment requirements
- **Regulation (EU) 2017/745** — Medical Device Regulation
- **21 CFR 820** — FDA Quality System Regulation (QSR / QMSR post-Feb 2026)
- **FDA Final Rule (Feb 2024)** — Quality Management System Regulation (incorporating ISO 13485 by reference)
- **AAMI TIR45:2012** — Guidance on use of agile practices in development of medical device software
- **IEC 62304:2006/A1:2015** — Medical device software lifecycle
- **GHTF / IMDRF guidance documents** — international harmonization context
