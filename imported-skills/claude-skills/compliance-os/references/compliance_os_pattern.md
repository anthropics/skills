# Compliance OS — The Meta-Framework Pattern

This reference answers exactly one decision: **when do we orchestrate frameworks vs run them separately, and what does the meta-framework architecture look like?**

## The Problem Compliance OS Solves

Most growing companies hit a wall: 2–3 compliance frameworks operating in parallel, each with its own tooling, its own audit calendar, its own evidence requirements, its own internal owner. The result:

- **Duplicate evidence collection** — access-review records assembled 3 times for ISO 27001, SOC 2, and ISO 42001 audits
- **Conflicting audit calendars** — surveillance audits stack in the same week with insufficient auditor capacity
- **Fragmented management review** — each framework wants its own management review, taking 5x the executive time
- **Inconsistent control taxonomies** — "access control" means slightly different things across SOC 2 and ISO 27001 Annex A and ISO 42001 Annex A
- **Unowned cross-framework gaps** — controls in framework A but not B fall to ad-hoc ownership
- **Evidence freshness mismatch** — ISO 27001 wants 12-month log retention, GDPR can want longer, leading to either over-retention or compliance gaps

Compliance OS is the orchestration layer that sits **above** per-framework skills and consolidates the cross-framework view.

## The Four Operations

```
                    [ Company Profile JSON ]
                              │
                              v
                  ╔═══════════════════════╗
                  ║ 1. CONFIGURE          ║   framework_selector.py
                  ║   "Which apply?"      ║
                  ╚═══════════════════════╝
                              │
                              v
                  ╔═══════════════════════╗
                  ║ 2. MAP                ║   cross_framework_mapper.py
                  ║   "What overlaps?"    ║
                  ╚═══════════════════════╝
                              │
                              v
                  ╔═══════════════════════╗
                  ║ 3. SIMULATE           ║   audit_simulator.py
                  ║   "What audit looks   ║
                  ║    like to fail?"     ║
                  ╚═══════════════════════╝
                              │
                              v
                  ╔═══════════════════════╗
                  ║ 4. CONSOLIDATE        ║   evidence_pool_generator.py
                  ║   "Where's the evidence║
                  ║    + what reuses?"    ║
                  ╚═══════════════════════╝
                              │
                              v
                    [ Multi-framework plan ]
```

Each operation is a stdlib Python tool with deterministic logic — no LLM calls, no hidden state.

## When to Use Compliance OS

| Situation | Use compliance-os? |
|---|---|
| Single framework only (e.g., just SOC 2) | No — the per-framework skill is sufficient |
| 2+ frameworks operating in parallel | Yes |
| Adding a new framework to existing program | Yes — for cross-framework reuse mapping |
| Planning annual audit calendar across multiple certifications | Yes |
| Onboarding a new AI system that triggers ISO 42001 + EU AI Act + GDPR | Yes |
| Acquiring a company with different compliance posture | Yes — for gap mapping post-acquisition |
| Internal-audit-only program (no external certification) | Yes if multi-framework; No if single |

## What Compliance OS Is NOT

- **NOT a per-framework deep-dive skill.** Per-framework skills (`ra-qm-team/skills/iso42001-specialist/`, etc.) do the operational work. Compliance OS orchestrates them.
- **NOT a GRC platform replacement.** GRC platforms (Drata, Vanta, OneTrust, Hyperproof, etc.) are tools that operationalize what compliance OS describes — they're complementary. Compliance OS gives the conceptual map; GRC tools store the evidence.
- **NOT a binding legal opinion.** Cross-framework mappings reflect published guidance from ISO, AICPA, NIST, IIA, EDPB. Novel cross-walks need outside counsel.
- **NOT a certification body.** Certification audits are performed by accredited bodies. Compliance OS prepares for them.

## Roles and Ownership

A multi-framework compliance program typically has these roles. Compliance OS does not replace them — it gives them a shared mental model.

| Role | Owns |
|---|---|
| **Compliance officer** | The meta-program; framework selector; cross-framework mapper; consolidated evidence pool |
| **CISO** | ISO 27001 + SOC 2 + cybersecurity slices of ISO 42001 + GDPR Article 32 |
| **DPO** | GDPR; privacy slice of ISO 42001 (A.7.6); EU AI Act Article 27 FRIA where applicable |
| **AIMS lead** | ISO 42001; AI-specific slice of EU AI Act Article 17 QMS |
| **QMS lead** | ISO 13485 / FDA QSR / EU MDR 745 (medical-device contexts) |
| **Risk manager** | ISO 14971 + AI risk per ISO 23894 |
| **Internal auditor(s)** | Clause 9.2 audit programmes across all frameworks |
| **Executive sponsor** | Management review (Clause 9.3) across all frameworks |

A typical mid-stage AI SaaS has compliance officer + CISO + DPO as the core trio; AIMS lead is a part-time hat.

## The Integrated Management System Pattern

When multiple management-system standards apply (ISO 27001 + ISO 42001 + ISO 9001/13485 + ISO 14001), the recommended structure is an **Integrated Management System (IMS)** rather than parallel siloed systems. The IMS pattern:

- Single scope statement covering all applicable standards
- Single policy set with framework-specific overlays (e.g., the AI policy required by ISO 42001 A.2.2 sits alongside the info-sec policy required by ISO 27001 A.5.1)
- Single document control procedure
- Single internal audit programme covering all standards over a rolling 3-year cycle
- Single management review covering all standards
- Single CAPA loop with framework-tagged nonconformities
- Per-framework deep-dive evidence under common umbrella

Compliance OS is the operating model for the IMS pattern.

## How Compliance OS Relates to Sectoral Programs

| Sectoral context | Compliance OS approach |
|---|---|
| Pure SaaS (no AI, no medical) | Skip compliance-os. Use ISO 27001 + SOC 2 + GDPR skills directly. |
| AI SaaS (EU users) | Use compliance-os. Frameworks: ISO 27001 + SOC 2 + ISO 42001 + EU AI Act + GDPR. |
| AI medical device | Use compliance-os. Frameworks: ISO 13485 + 14971 + 42001 + EU AI Act + EU MDR / FDA QSR + GDPR. Most complex case. |
| Financial / regulated industry | Use compliance-os + sectoral overlay (e.g., NYDFS, FINMA, NIS2). |

## Anti-Patterns to Avoid

1. **Building compliance-os before having ≥ 2 frameworks operating maturely.** Premature orchestration. Mature one framework first; layer the second; THEN orchestrate.
2. **Using compliance-os to bypass per-framework deep work.** The cross-framework mapping says "reuse evidence from framework A." That presumes framework A's evidence is solid. Reuse mapping ≠ skip diligence.
3. **Treating mapping confidence as binary.** HIGH confidence means same evidence; MEDIUM means existing evidence with overlay; LOW means concept overlap. LOW mappings still need new artefacts.
4. **Forgetting that bindings (regulations) outrank certifications.** GDPR + EU AI Act non-compliance carries actual penalties; ISO 27001 non-certification just blocks procurement. Sequence accordingly.
5. **Replacing the per-framework skill with compliance-os.** Compliance OS orchestrates; per-framework skills do the deep work.

## When This Reference Doesn't Help

- **Specific framework requirements.** See the per-framework skill.
- **GRC platform selection.** Tooling decision; commercial market evolves rapidly.
- **Per-sector regulatory deep-dive.** Use sectoral skills (financial, healthcare, etc.).

---

**Source authorities (non-exhaustive):**

- **ISO/IEC 19011:2018** — Guidelines for auditing management systems (the canonical audit standard for ISO-family certifications)
- **IIA International Professional Practices Framework (IPPF)** — Internal Audit Standards (Standards 1000-2600); attribute + performance standards
- **AICPA AT-C 105 + AU-C 240** — Trust Services + auditor's responsibility framework (SOC 2 + financial audit overlap)
- **COSO Enterprise Risk Management 2017** — Integrated framework for risk management across the enterprise
- **NIST Cybersecurity Framework 2.0** — profile pattern for organizing security/risk programmes (precedent for compliance-os approach)
- **ISO/IEC 27001:2022** — Information security management (foundational management system for most compliance programs)
- **ISO/IEC 17021** — Conformity assessment requirements (governs certification bodies; informs audit cycle)
- **ISACA** — *Auditing Artificial Intelligence* (2nd ed., 2024) — multi-framework AI audit guidance
- **ENISA** — *Multilayer Framework for Good Cybersecurity Practices for AI* (Mar 2023) — multi-layer integration
- **Annex SL of the ISO/IEC Directives** (2024) — the high-level structure shared by management system standards enabling integration
