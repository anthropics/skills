# Annex III High-Risk AI Categories + Article 6(2)–(3) Decision Tree

This reference answers exactly one decision: **for a given AI system, is it Annex III high-risk, and does any Article 6(3) carve-out apply?**

Pair with `scripts/ai_system_risk_classifier.py` for the decision-tree implementation.

## The Article 6 Decision Order

```
1. Article 5 — prohibited?         → YES: STOP. Prohibited. Cannot place on market.
2. Article 6(1) + Annex I product? → YES: high-risk per sectoral law (e.g., MDR 745 medical device with AI safety component)
3. Article 6(2) + Annex III?       → YES: enter Article 6(3) carve-out check
4. Article 6(3) carve-out applies?  → YES (and no profiling): NOT high-risk
                                    → NO  (or profiling present): high-risk
5. Article 50 transparency trigger? → YES: limited-risk
6. Default                          → minimal-risk
```

## Annex III — The 8 Categories (Article 6(2))

### §1 — Biometrics (the heaviest category)

- Remote biometric identification systems
- Biometric categorisation according to sensitive or protected attributes (where not prohibited under Article 5)
- Emotion recognition (where not prohibited under Article 5)

**Conformity assessment:** Module H (notified body required) per Article 43(1).

**Carve-out applicability:** Article 6(3) carve-outs do NOT apply to biometric ID systems performing biometric verification. Carve-out can apply to other Annex III §1 systems only if profiling is absent.

### §2 — Critical Infrastructure

- AI used as safety component in management/operation of road, rail, air, water, gas, electricity, heating

**Carve-out applicability:** rarely satisfied — safety components by definition affect critical operation.

### §3 — Education and Vocational Training

- Determining access, admission, or assignment to educational institutions
- Evaluating learning outcomes including in steering learning process
- Assessing appropriate level of education for an individual
- Monitoring and detecting prohibited behaviour during tests

**Carve-out applicability:** narrow procedural tasks (e.g., automatic answer-sheet OCR) may carve out; substantive evaluation does not.

### §4 — Employment, Workers Management, Self-Employment Access (a frequent trigger)

- Recruitment / selection (e.g., placing targeted job ads, screening applications, evaluating candidates)
- Decisions about promotion, termination, task allocation based on individual behaviour or traits
- Monitoring/evaluating performance + behaviour

**Carve-out applicability:** profiling of natural persons is always present in employment AI by definition (Article 6(3) last sentence overrides carve-out claim).

### §5 — Access to Essential Private and Public Services

- Public benefits and services (eligibility evaluation)
- Credit scoring of natural persons (with limited exception for fraud detection)
- Risk assessment + pricing of life and health insurance
- Emergency dispatch services (police, fire, ambulance) prioritisation

**Carve-out applicability:** profiling typically present; carve-out rare.

### §6 — Law Enforcement (high political sensitivity)

- Risk assessment of natural persons becoming offender or victim
- Polygraphs and similar
- Reliability evaluation of evidence
- Predictive policing (subject to Article 5 prohibition limits)
- Profiling of natural persons under Article 3(4) GDPR

**Carve-out applicability:** rarely applicable; political bar high.

### §7 — Migration, Asylum, Border Control Management

- Polygraphs and similar
- Risk assessment of natural persons crossing borders
- Examination of applications for asylum, visa, residence permits
- Identifying / verifying natural persons at borders (except routine document checks)

**Carve-out applicability:** rarely applicable.

### §8 — Administration of Justice and Democratic Processes

- Assisting judicial authority in interpretation of facts and law and applying law to facts
- Influencing the outcome of elections or referendums or natural persons' voting behaviour (excludes purely organizational/logistical uses)

**Carve-out applicability:** rarely applicable in substantive use; logistical electoral systems may carve out.

## Article 6(3) Carve-Out Test

Per Article 6(3), an Annex III AI system is NOT high-risk if **at least one** of these conditions is met AND no profiling occurs:

| Carve-out | Description | Example |
|---|---|---|
| **(a)** | Performs a narrow procedural task | Automatic spell-check on application forms |
| **(b)** | Improves the result of a previously completed human activity | Polish-up tool applied after human-drafted decision |
| **(c)** | Detects decision-making patterns or deviations from prior decision-making patterns without replacing or influencing the human assessment | Auditing tool that flags inconsistency in past human decisions but does not generate decisions |
| **(d)** | Performs a preparatory task to an assessment relevant for the purposes referred to in Annex III | Organizing applications by submission date before human review |

**Critical override (last sentence of Article 6(3)):** if the AI system performs **profiling of natural persons**, it remains high-risk regardless of carve-out claim. Profiling is defined by Article 4(4) of GDPR: any form of automated processing of personal data consisting of using personal data to evaluate certain personal aspects relating to a natural person.

In practice: most decision-support / decision-making AI involving natural persons performs profiling. Carve-out works for narrow procedural / preparatory / aggregation tools, not for substantive evaluation.

## Provider's Article 6(4) Documentation Duty

If a provider claims Article 6(3) carve-out for an Annex III system, the provider must:
1. Document the rationale before placing on market
2. Register the system in the EU database (Article 71)
3. Make documentation available to national competent authorities on request

Failure to document the carve-out claim properly is itself a compliance failure subject to Article 99 penalties.

## Real-World Decision Heuristic

For each AI system, ask in order:

1. **Does it touch hiring, credit, insurance, education, law enforcement, migration, justice, or critical infrastructure?** If yes, continue. If no, skip to step 4.
2. **Does it influence (not just inform) decisions about natural persons?** If yes → high-risk per Annex III. Conformity assessment required.
3. **If it only informs / does narrow procedural work AND there's no profiling:** carve-out may apply. Document thoroughly. Still register if Annex III §1 / §6 / §7.
4. **Does it interact directly with natural persons, generate synthetic content, or do emotion recognition outside Article 5?** Article 50 transparency applies (limited-risk).
5. **Otherwise:** minimal-risk.

## When This Reference Doesn't Help

- **Whether a system is "an AI system" at all (Article 3(1)).** See Commission Guidelines Feb 2025.
- **Annex I sectoral product law overlap.** See sectoral regulation (MDR 745, machinery, toys, etc.).
- **GPAI separate track.** See `gpai_obligations.md`.

---

**Source authorities (non-exhaustive):**

- **Regulation (EU) 2024/1689** — Articles 5, 6, 7 and Annex III (binding text)
- **European Commission** — Guidelines on prohibited AI practices (Feb 2025)
- **European Commission** — Article 6(3) implementing guidelines (expected; check current Commission communications)
- **European Data Protection Board** — Opinion 28/2024 (Article 6 GDPR + AI Act interaction)
- **EDPS** — interpretive guidance on biometric and profiling provisions
- **Future of Life Institute** — Annex III decision tree (community reference)
- **IAPP EU AI Act Tracker** — running practitioner interpretation
- **National AI authorities** (per Article 70) — emerging Member State guidance: BfDI (Germany), CNIL (France), AEPD (Spain) AI position papers
