# AI Compliance Officer

An AI-powered compliance skill that reviews marketing content, emails, landing pages, and privacy policies against 208 regulatory rules across 8 frameworks.

## What It Does

Feed it any marketing content — text, a URL, an email, or a privacy policy — and it reviews it against real regulations, citing specific laws with direct links to the source text.

**Frameworks covered:**

| Framework | Rules | Jurisdiction |
|-----------|-------|-------------|
| FTC | 95 | US |
| HIPAA | 17 | US |
| GDPR | 25 | EU |
| SEC 482 | 15 | US |
| SEC Marketing | 18 | US |
| CCPA | 12 | US-CA |
| COPPA | 12 | US |
| CAN-SPAM | 14 | US |

**6 capabilities in one skill:**

- **Review content** — Check marketing copy, landing pages, or ads for violations
- **Check email** — Email-specific compliance (CAN-SPAM, opt-out, sender ID, dark patterns)
- **Check privacy policy** — Disclosure checklist against GDPR, CCPA, HIPAA, COPPA
- **Explain rule** — Look up any rule and get a plain-English explanation
- **List rules** — Browse and filter the full rule database
- **Draft disclosures** — Generate ready-to-use compliance language

## Installation

### Claude Code (Plugin Marketplace)

```
/plugin marketplace add QCME-AI/agentic-compliance-rules
```

### ClawHub

```
openclaw skill install compliance-officer
```

### Manual

Copy the `compliance-officer/` directory into your project's `.claude/skills/` folder:

```bash
cp -r compliance-officer/ .claude/skills/compliance-officer/
```

## Example Usage

**Review marketing copy:**
```
Check this for compliance: "Our supplement is clinically proven to cure diabetes. Results guaranteed! - Dr. Smith, Board Certified"
```

**Check a landing page:**
```
Review https://example.com/promo for compliance issues
```

**Check an email:**
```
Check this email: Subject: "URGENT! Last chance!" From: deals@shop.com Body: "Click to claim your FREE gift..."
```

**Review a privacy policy:**
```
Check the privacy policy at https://example.com/privacy
```

**Explain a rule:**
```
Explain rule FTC-255-5-material-connection
```

## How It Works

This skill provides structured regulatory knowledge — not regex matching. The rules describe what each regulation requires, what violations look like, and how to fix them. The AI reads these definitions and reasons about your content holistically, citing the actual CFR section or statute.

## Source

Open source under Apache 2.0. Full rule database and contributing guide at:
https://github.com/QCME-AI/agentic-compliance-rules

## Disclaimer

Findings are potential issues for human review, not definitive legal violations. Your compliance and legal teams have final authority.
