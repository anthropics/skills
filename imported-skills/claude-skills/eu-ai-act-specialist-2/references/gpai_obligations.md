# GPAI Obligations — Articles 51–55 + Annex XI–XIII

This reference answers exactly one decision: **is a foundation model a GPAI, does it have systemic risk, and what obligations apply?**

## What is GPAI?

Per **Article 3(63)**, a "general-purpose AI model" is:

> an AI model, including where such an AI model is trained with a large amount of data using self-supervision at scale, that displays significant generality and is capable of competently performing a wide range of distinct tasks regardless of the way the model is placed on the market and that can be integrated into a variety of downstream systems or applications.

In practice: foundation models such as large language models, multimodal models, diffusion models for image/video generation. The distinguishing characteristic is generality + integration into downstream systems.

GPAI is governed by **Title V** (Articles 51–55), separate from the high-risk AI system regime in Title III. A given application can simultaneously be a GPAI provider AND a high-risk system provider (e.g., a downstream provider fine-tuning a foundation model for credit scoring).

## Systemic-Risk GPAI Designation (Article 51)

A GPAI model is presumed to have systemic risk if **either**:

- **Article 51(1)(a):** trained with compute > 10²⁵ floating-point operations (FLOPs), OR
- **Article 51(1)(b):** designated by Commission decision based on Annex XIII criteria

**Article 51(3)** provides a list of Annex XIII criteria for designation: model capabilities, parameter count, dataset size + quality, autonomy, modalities, scalability, reach to internal market, registered business users.

A provider may contest a presumption (Article 52) by submitting evidence to Commission. Commission may also designate a model with systemic risk even if below the FLOPs threshold.

## Article 53 — Obligations for ALL GPAI Providers

In force from 2 Aug 2025.

| Article | Obligation |
|---|---|
| **53(1)(a)** | Draw up and keep up-to-date technical documentation of the model (per Annex XI) — model architecture, training process, training compute, energy consumption, evaluation results, limitations |
| **53(1)(b)** | Make information available to downstream providers integrating the model (per Annex XII) — intended uses, technical means for integration, computational + hardware requirements |
| **53(1)(c)** | Put in place policy to comply with EU copyright law (training data + outputs) |
| **53(1)(d)** | Draw up and publicly publish a sufficiently detailed summary about content used for training |

**Annex XI items (technical documentation for GPAI):**

1. General description of GPAI model (intended tasks, architecture, integration paradigm)
2. Detailed description (training process, design choices, training data sources, energy consumption)
3. Training process (compute, data, methodology)
4. Information for downstream providers

**Annex XII items (transparency to downstream providers):**

1. General description (capabilities, modalities, intended uses)
2. Acceptable use policy
3. Technical means + computational requirements
4. Evaluation results + limitations

## Article 54 — Authorized Representative for Non-EU GPAI Providers

GPAI providers established outside the EU must appoint, by written mandate, an authorized representative established in the EU. The representative:

- Holds the technical documentation (Annex XI)
- Holds the information for downstream providers (Annex XII)
- Cooperates with AI Office and national authorities
- May terminate the mandate if provider refuses to cooperate with Article 53 obligations

This parallels the Article 22 representative obligation for non-EU providers of high-risk AI systems.

## Article 55 — Additional Obligations for Systemic-Risk GPAI

Applies only to GPAI designated under Article 51.

| Obligation | Detail |
|---|---|
| **Model evaluations** | Including adversarial testing — identify + mitigate systemic risks |
| **Systemic risk assessment** | Track risk along entire lifecycle |
| **Serious incident reporting** | Document + report serious incidents and possible corrective measures to AI Office without undue delay |
| **Cybersecurity** | Ensure adequate level of cybersecurity protection for the model + the physical infrastructure |

Penalties for systemic-risk GPAI non-compliance: up to EUR 15M or 3% of worldwide annual turnover per Article 101.

## Code of Practice (Article 56) — Bridging Instrument

The AI Office facilitates a **Code of Practice** for GPAI providers covering Article 53 and 55 obligations. The Code is voluntary but provides a presumption of compliance. The first Code is expected to be finalised by 2 Aug 2025 (with iteration thereafter).

**Practical implication:** until harmonised standards are published under Article 40 for GPAI (not yet available as of mid-2026), the Code of Practice is the primary "what does compliance look like" reference.

## Provider-of-System vs Provider-of-Model Boundaries

A common ambiguity: when does a downstream provider become a GPAI provider in their own right?

Per **Article 25(3)**: a downstream provider that **substantially modifies** a GPAI model (e.g., extensive fine-tuning that changes the model's intended purpose) becomes a GPAI provider with its own Article 53 obligations.

Per **Article 25(1)**: if a downstream provider integrates a GPAI model into a high-risk AI system, the downstream provider remains the high-risk AI system's provider with Title III obligations; the GPAI model's provider retains its Article 53 + (if applicable) Article 55 obligations.

The Commission Q&A and emerging Code of Practice provide more detail on "substantial modification" boundary.

## Practical Decision Tree

```
Is the model a GPAI per Article 3(63)?
   ├─ No  → Not GPAI. Apply standard high-risk rules if applicable.
   └─ Yes → Article 53 obligations apply.
            └─ Training compute > 10^25 FLOPs OR Commission-designated?
                  ├─ No  → Article 53 only.
                  └─ Yes → Article 53 + Article 55 (systemic-risk additional obligations).
```

## When This Reference Doesn't Help

- **Article 5 prohibitions applied to GPAI use cases.** See `eu_ai_act_titles.md` Title II.
- **Article 40 harmonised standards for GPAI.** Not published as of mid-2026; CEN-CENELEC JTC 21 work in progress.
- **Open-source GPAI carve-out (Article 53(2)).** GPAI models released under free + open-source license can be exempt from some Article 53 obligations IF they do not have systemic risk. Article 53(2) specifies the exact exemption scope.

---

**Source authorities (non-exhaustive):**

- **Regulation (EU) 2024/1689** — Articles 3(63), 51–55, Annex XI–XIII (binding)
- **European AI Office** — GPAI Code of Practice (published in drafts during 2024–2025)
- **European Commission** — GPAI guidance Q&A
- **NIST** — Generative AI Profile (NIST AI 600-1, July 2024) — voluntary US guidance with conceptual overlap to Article 55 model-evaluation requirements
- **Stanford CRFM** — Foundation Model Transparency Index (2023–) — practitioner benchmark of GPAI disclosure practices
- **MIT** — AI Risk Repository (continuously updated)
- **IAPP** — GPAI Tracker section of EU AI Act Tracker
- **Open Future / Knowledge Rights 21** — Code of Practice + copyright analysis (civil society input)
- **Mozilla / Hugging Face / GitHub** — open-source GPAI submissions to the Commission consultation on Article 53(2) exemption
