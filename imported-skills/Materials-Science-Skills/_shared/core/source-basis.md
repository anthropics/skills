# Source Basis

This file documents the authoritative sources behind each shared rule in
`_shared/core/`. Every behavioral rule can be traced back to one of the
source categories below.

---

## 1. Stance and operating principles

**Source authority: Conservative local synthesis**

The operating stance (`stance.md`) is a local synthesis from:
- Academic publishing best practices (avoid fabrication, evidence-based claims)
- Materials journal author guidelines (CBM, CCC, RMPD, JBE, Nature Materials, Advanced Materials, Acta Materialia, ACS Nano Guide for Authors)
- Institutional research integrity training materials

The "never invent" prohibition list and five-question reasoning logic are
original local rules designed to prevent common failure modes observed in
Chinese-authored materials manuscripts. They do not quote any single
external source verbatim.

## 2. Evidence contract

**Source authority: Journal editorial standards + academic publishing norms**

The evidence contract (`evidence-contract.md`) derives from:

| Rule category | Source | Authority level |
|---|---|---|
| Claim-evidence ladder | Standard academic evidence hierarchy (systematic review > experiment > observation) | Academic convention |
| Minimum support table | CBM/CCC/RMPD/JBE/Advanced Materials/Acta Materialia Guide for Authors sections on manuscript requirements | Official journal policy |
| Anti-overclaim verbs | Hedging best practices in academic English (Hyland 1998, "Hedging in Scientific Research Articles") | Published research |
| Sustainability language | Journal of Cleaner Production editorial policy on environmental claims; ISO 14040/14044 LCA framework | Official standard + policy |
| Missing evidence flags | Local convention; no external source | Conservative local |

## 3. Claim-strength ladder

**Source authority: Academic hedging research + journal editorial practice**

| Rule | Source | Authority level |
|---|---|---|
| Verb downgrade table | Hyland (1998) hedging taxonomy; Nature "Writing with Style" guidelines | Published research + editorial guide |
| Evidence tiers | Adapted from Cochrane evidence hierarchy for materials science | Adapted standard |
| Materials red flags | Derived from CBM/CCC/Advanced Materials/Acta Materialia common reviewer comments (overclaim patterns) | Conservative local synthesis |
| Negative result handling | APA Publication Manual (7th ed.) on reporting non-significant results | Official standard |

## 4. Terminology ledger

**Source authority: Academic writing best practice**

| Rule | Source | Authority level |
|---|---|---|
| One-name-per-one-thing | Standard technical writing principle (ISO 704:2022 Terminology work) | Official standard |
| Ledger-before-drafting | Nature "Writing with Style" consistency guidance | Editorial guide |
| Chinese-English mapping | GB/T 7714-2015 national standard terminology; journal-specific usage | Official standard + observation |
| No-invent-terms | Nature editorial policy on nomenclature | Official policy |

## 5. Ethics and AI boundaries

**Source authority: Nature editorial policies + institutional AI-use guidelines**

| Rule | Source | Authority level |
|---|---|---|
| Citation ethics | Nature "Availability of data, material, code and the reproducibility agenda" | Official editorial policy |
| AI traffic-light boundary | Nature "Artificial Intelligence and the Future of Publishing" (2023); Springer Nature AI policy | Official editorial policy |
| Materials prohibitions | Local rules derived from common reviewer complaints | Conservative local |
| Proofreading checks | Standard copyediting practice | Industry convention |

---

## Implementation notes

1. **Official standard / editorial policy**: Rules derived from these sources
   are treated as authoritative. Deviating from them requires explicit justification.

2. **Published research**: Rules from peer-reviewed publications on academic
   writing are treated as well-supported but open to interpretation.

3. **Conservative local**: Rules labeled "conservative local" are our own
   additions that go beyond what any external source strictly requires.
   They exist to prevent common failure modes in practice. They can be
   relaxed if evidence shows they are too restrictive.

4. When in doubt about a rule's authority, the instruction is to
   **state the limit rather than improvise beyond it**. If a user asks
   for something that conflicts with an official standard, quote the
   standard and let the user decide.
