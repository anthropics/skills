# Cross-Framework Overlap — The 9-Framework × Control-Family Matrix

This reference answers exactly one decision: **for each common control family, which of the 9 supported frameworks address it, and at what confidence?**

Pair with `scripts/cross_framework_mapper.py` for the deterministic lookup.

## The 9 Frameworks

| ID | Standard | Type |
|---|---|---|
| iso_27001 | ISO/IEC 27001:2022 + Annex A | Certifiable management system (info-sec) |
| iso_13485 | ISO 13485:2016 | Certifiable management system (medical device QMS) |
| iso_42001 | ISO/IEC 42001:2023 | Certifiable management system (AIMS) |
| iso_14971 | ISO 14971:2019 | Process standard (medical device risk management) |
| eu_ai_act | Regulation (EU) 2024/1689 | Binding regulation (AI) |
| eu_mdr_745 | Regulation (EU) 2017/745 | Binding regulation (medical devices) |
| gdpr | Regulation (EU) 2016/679 | Binding regulation (privacy) |
| soc_2 | AICPA SOC 2 TSC | Attestation (US enterprise procurement) |
| fda_qsr | FDA 21 CFR 820 | Binding regulation (US medical devices) |

## Highest-Overlap Pairs (where reuse leverage is maximized)

1. **ISO 27001 ↔ SOC 2** — densest known overlap. ISO 27001:2022 Annex A 93 controls map to SOC 2 TSC ~75% by published cross-walks. The 19 merged controls in `cross_framework_mapper.py` cite 51 atomic ISO 27001 + 34 atomic SOC 2 controls in HIGH-confidence themes. Adding SOC 2 on top of certified ISO 27001 is typically ~3 months of incremental work.
2. **ISO 13485 ↔ FDA QSR** — harmonised in 2024 (FDA Quality Management System Regulation rule). Most evidence reuses.
3. **ISO 42001 ↔ ISO 27001** — 60% reuse: most Clauses 4–10 evidence transfers with AI scope appended; Annex A controls A.7 (data) + A.10 (third-party) overlap heavily; the 40% net-new is mostly A.5 (impact assessment) + A.6 (lifecycle) + A.9 (use of AI systems).
4. **EU AI Act Article 17 ↔ ISO 42001** — ISO 42001 satisfies most of Article 17(1)(a)–(m) QMS requirements. The cross-walk in `compliance-team-iso42001/references/cross_framework_mapping_ai.md` provides Article 17 line-item mapping.
5. **GDPR ↔ ISO 27001 Annex A.5.34** — privacy by design overlap; GDPR Article 32 technical and organizational measures maps to ISO 27001 cryptography (A.8.24) + access control (A.5.15) + incident response (A.5.24).

## Control Family Overlap Matrix (summary)

Legend: ✅ direct overlap; 🔶 partial overlap with overlay; ⚠️ concept overlap only; ⛔ not applicable.

| Control family | 27001 | 13485 | 42001 | 14971 | EU AI Act | MDR | GDPR | SOC 2 | FDA QSR |
|---|---|---|---|---|---|---|---|---|---|
| Access control | ✅ | 🔶 | 🔶 | ⛔ | ⛔ | ⛔ | 🔶 | ✅ | 🔶 |
| Asset inventory | ✅ | ✅ | ✅ | ⛔ | ⛔ | ⛔ | 🔶 | ✅ | ✅ |
| Risk management | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | 🔶 | ✅ | 🔶 |
| Supplier mgmt | ✅ | ✅ | ✅ | ⛔ | 🔶 | 🔶 | ✅ | ✅ | 🔶 |
| Incident response | ✅ | ✅ | 🔶 | 🔶 | 🔶 | ✅ | ✅ | ✅ | ✅ |
| Logging & monitoring | ✅ | 🔶 | 🔶 | ⛔ | 🔶 | 🔶 | ⚠️ | ✅ | 🔶 |
| Change management | ✅ | ✅ | 🔶 | ⛔ | ⛔ | ✅ | ⛔ | ✅ | ✅ |
| BCP / DR | ✅ | 🔶 | ⛔ | ⛔ | ⛔ | ⛔ | ⛔ | ✅ | ⛔ |
| Competence + training | ✅ | ✅ | ✅ | ⛔ | 🔶 | ✅ | ⛔ | ✅ | ✅ |
| Data governance | 🔶 | ✅ | ✅ | ⛔ | ✅ | ⚠️ | ✅ | ⚠️ | 🔶 |
| Internal audit | ✅ | ✅ | ✅ | ⛔ | ⛔ | 🔶 | ⛔ | ✅ | 🔶 |
| Management review | ✅ | ✅ | ✅ | ⛔ | ⛔ | 🔶 | ⛔ | 🔶 | ⛔ |
| Cryptography | ✅ | ⛔ | ⛔ | ⛔ | ⛔ | ⛔ | ✅ | ✅ | ⛔ |
| Secure SDLC | ✅ | ⛔ | 🔶 | ⛔ | 🔶 | ⛔ | ⛔ | ✅ | ⛔ |
| Vulnerability mgmt | ✅ | ⛔ | ⛔ | ⛔ | ⛔ | ⛔ | ⛔ | ✅ | ⛔ |
| Physical security | ✅ | ✅ | ⛔ | ⛔ | ⛔ | ✅ | ⛔ | ✅ | ✅ |
| Personal data protection | ✅ | ⛔ | 🔶 | ⛔ | 🔶 | ⛔ | ✅ | 🔶 | ⛔ |
| Documentation control | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | 🔶 | ✅ | ✅ |
| Continual improvement / CAPA | ✅ | ✅ | ✅ | ✅ | ⛔ | ✅ | ⛔ | ✅ | ✅ |

## How to Use This Matrix

1. **Identify the union** of applicable frameworks (from `framework_selector.py`)
2. **For each control family**, find the row and read the columns for your frameworks
3. **Build evidence once** for the framework with the strongest requirement, then reuse-with-overlay for others
4. **Document the reuse mapping** in your compliance program documentation so auditors can trace evidence to framework controls

## Practical Reuse Sequencing

If you operate ISO 27001 (mature) and add a second framework:

| Add | Reuse leverage from 27001 |
|---|---|
| **SOC 2** | ~75% — heaviest reuse; the canonical pair |
| **ISO 42001** | ~60% — Clauses 4–10 reuse strong; Annex A.7/A.10 reuse strong; A.5/A.6/A.9 net-new |
| **GDPR** | ~50% — Article 32 organizational measures reuse; Articles 5/6/30 net-new privacy work |
| **EU AI Act** | ~40% — Article 17 QMS via ISO 42001 path; Articles 9/10 net-new; transparency net-new |
| **ISO 13485** | ~30% — document control + CAPA reuse; design controls + medical specifics net-new |
| **FDA QSR** | ~30% — via ISO 13485 path; sectoral overlay |
| **EU MDR 745** | ~25% — most net-new (technical documentation, clinical evidence, UDI) |
| **ISO 14971** | ~20% — process standard, integrates with 13485 |

## Confidence Levels Explained

The `cross_framework_mapper.py` returns one of three confidence levels per mapping:

- **HIGH (H)** — same evidence satisfies both framework controls without modification. Example: a quarterly access-review record satisfies ISO 27001 A.5.15 + SOC 2 CC6.1 simultaneously.
- **MEDIUM (M)** — existing evidence plus a framework-specific overlay. Example: ISO 27001 supplier-management procedure adapted to add AI-specific clauses for ISO 42001 A.10.2.
- **LOW (L)** — concept overlap only; new artefact required. Example: ISO 42001 A.5.2 impact assessment uses concepts from GDPR DPIA but is a separate artefact.

## When This Reference Doesn't Help

- **Specific atomic control numbers.** See the per-framework skill's references.
- **Sector-specific overlays.** See sectoral skills (financial, healthcare).
- **Audit simulation depth.** See `audit_simulation_methodology.md`.

---

**Source authorities (non-exhaustive):**

- **ISO/IEC 27001:2022** + Annex A (the foundational pair source)
- **ISO/IEC 42001:2023** + Annex A
- **AICPA Trust Services Criteria** (2017 + 2022 update)
- **Regulation (EU) 2024/1689** (EU AI Act)
- **Regulation (EU) 2016/679** (GDPR)
- **Regulation (EU) 2017/745** (EU MDR)
- **ISO 13485:2016**
- **ISO 14971:2019**
- **FDA 21 CFR 820** (QSR) — harmonised under the FDA Quality Management System Regulation rule (effective 2026)
- **NIST SP 800-53 Rev 5** — security and privacy controls catalog (cross-walk reference)
- **NIST CSF 2.0** — profile pattern
- **ISACA** — *Mapping ISO 27001 to SOC 2* (continually updated)
- **CIS Controls v8** — additional cross-walk
- **CSA STAR** — cloud-specific cross-walk
