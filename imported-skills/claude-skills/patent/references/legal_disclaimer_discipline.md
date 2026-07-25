# Legal Disclaimer Discipline — When + Why Mandatory

This reference answers exactly one decision: **for which sub-use-cases does the patent skill require a legal disclaimer in the DOCX, and what does the disclaimer need to say?**

## The Core Rule

Patent law has **immediate financial + legal consequences**. The skill produces **search signal**, not legal advice. A reader who confuses the two and skips attorney consultation can face:

- Patent infringement liability (FTO failure → lawsuit)
- Patent application rejection (novelty failure → expensive abandoned application)
- Wasted R&D investment (proceeding on a confidence the search couldn't actually justify)

**The disclaimer is a safety property**, comparable to drafts-only in inbox-triage. It prevents foreseeable user harm.

## When Disclaimer Is Mandatory

| Sub-use-case | Disclaimer mandatory? | Rationale |
|---|---|---|
| **Novelty search** | YES (Q6 triggers it) | Prosecution decisions have legal consequences |
| **Freedom-to-operate** | YES (Q6 triggers it) | Shipping decisions have liability consequences |
| **Competitive landscape** | Optional (recommended) | Lower legal exposure; more strategic than legal |
| **Acquisition diligence** | Optional (strongly recommended) | M&A context — legal review usually already part of process |
| **Litigation prior-art** | Optional (strongly recommended) | Litigation context — counsel almost always involved |

For **mandatory** sub-use-cases, the disclaimer:
1. Appears in **Executive Summary** footer (Section 1)
2. Appears in **Strategy + Recommendations** body (Section 7)
3. Appears in **Audit Log** as a final reminder (Section 8)

For **optional** sub-use-cases, the disclaimer appears only in Section 8 as a reminder.

## What the Disclaimer Says

### Mandatory version (novelty + FTO)

> **⚖️ Legal Disclaimer:** This document is **search signal, not legal advice**. The verdict ({NOVEL/CLEAR/etc.}) is a technical assessment based on the patents found in this session's tool calls. **Patent novelty and freedom-to-operate determinations have legal consequences and require qualified counsel.**
>
> **Before any filing or licensing decision:**
> - Consult a registered patent attorney in your jurisdiction(s)
> - Provide them this dossier as starting material; they will conduct independent verification + opinion
> - Their opinion is privileged and admissible; this skill's output is neither
>
> The skill does not establish attorney-client privilege. The skill's verdict does not constitute a legal opinion.

### Optional version (landscape, diligence, litigation)

> **⚖️ Reminder:** This document is search signal. Patent attorney consultation is recommended for any decisions arising from this analysis.

## Why Disclaimer Discipline Matters

### Reason 1: Legal liability framing

Without disclaimer, a user could (in extreme cases) claim the skill misled them into a legal decision. Disclaimer makes the skill's role unambiguous: **technical assessment, not legal opinion**.

### Reason 2: Setting realistic expectations

Even a well-executed patent search has limits:

- Some patents may not be indexed in queried sources (especially recent applications)
- Some patents may be classified in unexpected CPC classes
- Some art may be in non-patent literature (academic papers, products, manuals)
- Some art may be in different languages (non-English jurisdictions)

The disclaimer tells the user: "I did the best technical search I could; counsel will catch what I might have missed."

### Reason 3: Privileged communication

Attorney-client conversations are **privileged** — not admissible against the user in litigation. This skill's output is **not privileged**. If the user later faces litigation, opposing counsel can subpoena the dossier as evidence of what the user knew.

The disclaimer reminds users to NOT rely solely on the dossier for high-stakes decisions; an attorney's opinion provides privilege.

### Reason 4: Jurisdiction-specific nuance

Patent law varies by jurisdiction:

- **First-to-file vs first-to-invent** (US switched to first-to-file in 2013; some countries differ)
- **Grace periods** (US has 1-year; many countries have none)
- **Doctrine of equivalents** (varies by jurisdiction)
- **Inequitable conduct** (US-specific; may affect prosecution strategy)

The skill cannot capture all jurisdictional nuance. Counsel can.

## Anti-Patterns

### Skipping disclaimer because user said "I'm a patent attorney"

The user might be a patent attorney, but they might also be running this for a less-experienced colleague or client. The disclaimer is **always** in the document because the document might outlive the original requester.

### Burying disclaimer in fine print

Mandatory-sub-use-case disclaimer appears in Sections 1, 7, and 8 — three locations. Reader cannot miss it.

### Replacing disclaimer with "consult your attorney"

The disclaimer must be specific about what the skill does and doesn't claim. "Consult your attorney" alone is insufficient; the disclaimer also needs to clarify:
- What the verdict means (technical assessment)
- What counsel adds (privilege, jurisdiction expertise, opinion)
- What's not covered (non-patent prior art, language coverage gaps)

### Conflating disclaimer with legal-advice disclaimer

Some skills use generic "this is not legal advice" boilerplate. The patent skill's disclaimer is specifically about patent novelty/FTO determinations and the role of qualified counsel — not generic.

### Removing disclaimer to "make the document feel more authoritative"

Authority comes from technical rigor (claim-text extraction, family resolution, CPC class follow-up), not from omitting safety disclaimers. The disclaimer **enhances** authority by making the skill's role transparent.

## Operational Checklist

For novelty + FTO (mandatory):

- [ ] Disclaimer in Executive Summary (Section 1) footer
- [ ] Disclaimer in Strategy section (Section 7)
- [ ] Disclaimer in Audit Log (Section 8) as final reminder
- [ ] Disclaimer text matches template above (don't paraphrase the legal language)
- [ ] Q6 attorney-status answer recorded in audit log

For landscape + diligence + litigation (optional):

- [ ] Reminder version in Audit Log (Section 8)
- [ ] Strategy section (Section 7) includes "consult patent attorney for [decision-specific context]"

## Citations (7 sources)

1. **MPEP §1.4 + §1.5 — *Manual of Patent Examining Procedure* (USPTO).** Source for the role of registered patent attorneys/agents in prosecution. The disclaimer's reference to "qualified counsel" tracks USPTO's registration framework.

2. **AIPLA *Code of Ethics* — American Intellectual Property Law Association.** Source for the privileged-communication framing. AIPLA's guidance on lay-vs-attorney communication informs the "this skill is not privileged" disclaimer language.

3. **35 USC §282 — *Presumption of validity*.** US patent statute. Source for understanding what "valid" means legally + why a search-signal verdict is not a legal validity opinion.

4. **35 USC §271 — *Infringement of patent*.** Source for the FTO disclaimer framing. Liability for infringement is a legal determination; the skill's "CLEAR/FLAGGED/HIGH RISK" verdict is technical.

5. **EPO Guidelines for Examination, Part E.** Source for European-jurisdiction differences (no grace period, different inventive-step analysis). The disclaimer's "jurisdiction-specific nuance" caveat tracks these variations.

6. **PCT Article 39 — Patent Cooperation Treaty.** Source for the cross-jurisdiction prosecution complexity that justifies counsel involvement. PCT national-phase entries each require local-counsel coordination.

7. **Fischer, T., & Henkel, J., "Patent Trolls on Markets for Technology" — *Research Policy* 41(9), 2012.** Empirical evidence for the cost of FTO mistakes. Patent assertion entities (PAEs) have made FTO failures financially severe; the disclaimer's emphasis on counsel reflects this risk reality.
