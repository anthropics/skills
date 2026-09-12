---
name: compliance-officer
description: >
  Reviews marketing content against FTC, HIPAA, GDPR, SEC 482, SEC Marketing, CCPA, COPPA, and
  CAN-SPAM — 208 specific laws with URLs.
license: Apache-2.0
compatibility: Requires network access for URL fetching. Works with Claude Code and similar agents.
metadata:
  author: qcme
  version: "1.0.0"
  source: https://github.com/QCME-AI/agentic-compliance-rules
---

# Compliance Officer

Check marketing content against 208 regulations across FTC, HIPAA, GDPR, SEC, CCPA, COPPA, and CAN-SPAM. Cites actual laws with source URLs.

## What You Can Do

- **Review marketing content** — paste copy, a URL, or an image
- **Check emails** — evaluate subject lines, bodies, and footers for CAN-SPAM and more
- **Audit privacy policies** — check for required disclosures across GDPR, CCPA, HIPAA, COPPA
- **Explain any rule** — look up a rule by ID and get a plain-English breakdown
- **Draft disclosures** — generate compliant disclosure language for your content

## Examples

Review a landing page:
```
Review this for compliance: "Lose 30 lbs in 2 weeks — GUARANTEED.
Clinically proven. Doctor recommended. Only 3 left in stock!"
```

Check an email:
```
Check this email for CAN-SPAM compliance: Subject: "URGENT: Act now!"
From: deals@shop.com Body: "Click to claim your FREE gift..."
```

Audit a privacy policy:
```
Review our privacy policy for GDPR and CCPA compliance: https://example.com/privacy
```

Look up a rule:
```
Explain rule FTC-255-5-material-connection
```

Draft disclosures:
```
Draft disclosure language for this influencer post: "Love this protein powder!
Use code SARAH20 for 20% off"
```

## Frameworks Covered

| Framework | Rules | Scope |
|-----------|-------|-------|
| FTC | 95 | Endorsements, claims, dark patterns, pricing |
| GDPR | 25 | Consent, disclosure, data rights, cookies |
| SEC Marketing | 18 | Investment adviser marketing |
| HIPAA | 17 | Health data, PHI, notice requirements |
| SEC 482 | 15 | Investment company advertising |
| CAN-SPAM | 14 | Email marketing, opt-out, sender ID |
| CCPA | 12 | California privacy, opt-out rights |
| COPPA | 12 | Children's privacy, parental consent |

## Install

```
npx clawhub install compliance-officer
```

## Source

Apache-2.0 — [github.com/QCME-AI/agentic-compliance-rules](https://github.com/QCME-AI/agentic-compliance-rules)

---

*For agent instructions, see `references/instructions.md`.*
