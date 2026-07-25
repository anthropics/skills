# Deliverability Guide

A cold email that lands in spam is worse than no email at all — it damages your sender reputation for future sends. Get deliverability right before you worry about copy.

---

## The Deliverability Stack

Email deliverability is a layer cake. Every layer has to be correct:

```
Domain reputation      (is your domain trusted by inbox providers?)
        ↓
Authentication         (SPF, DKIM, DMARC — are you who you say you are?)
        ↓
Sending infrastructure (IP reputation, sending limits, ramp-up)
        ↓
List quality           (are you sending to real, active addresses?)
        ↓
Email content          (does the content look like spam?)
        ↓
Engagement signals     (opens, replies, not-spam clicks)
```

Fix problems from the bottom up. No point perfecting copy if your domain is blacklisted.

---

## Domain Setup

### Use a Dedicated Sending Domain

Never send cold email from your primary company domain (`acme.com`). If your cold email domain gets flagged or blacklisted, you lose your main domain's email reputation.

**Setup options:**
- `mail.acme.com` — subdomain of main domain
- `acme-hq.com` — separate domain with similar name
- `getacme.com` / `tryacme.com` — common pattern for SaaS

**Rules for the sending domain:**
- Set up a proper website (even a simple redirect to main site) — bare domains look suspicious
- Match the company name visually — unrelated domains look like phishing
- Get a G Suite / Microsoft 365 mailbox on it — shared hosting email servers have worse reputation

### SPF Record

SPF (Sender Policy Framework) tells receiving servers which IP addresses are allowed to send email from your domain. Without it, your emails look unauthenticated.

**DNS TXT record:**
```
v=spf1 include:_spf.google.com ~all
```

Replace `_spf.google.com` with your sending provider's SPF include. Check your provider's documentation for the exact value (Google Workspace, SendGrid, Mailgun, etc. all have their own).

**Important:** Only have ONE SPF record per domain. If you have multiple, they conflict and authentication fails.

### DKIM

DKIM (DomainKeys Identified Mail) adds a cryptographic signature to your emails, proving they weren't tampered with in transit.

Setup is done through your email provider — they give you a DNS TXT record to add. It looks like:

```
google._domainkey.yourdomain.com  IN  TXT  "v=DKIM1; k=rsa; p=MIGfMA0..."
```

The public key in that record lets receiving servers verify your email's signature.

### DMARC

DMARC ties SPF and DKIM together and tells receiving servers what to do when authentication fails.

**Starter DMARC record (monitoring mode):**
```
_dmarc.yourdomain.com  IN  TXT  "v=DMARC1; p=none; rua=mailto:dmarc@yourdomain.com"
```

`p=none` means monitor but don't block — good to start with. Once you've confirmed SPF and DKIM are working cleanly, move to `p=quarantine` or `p=reject`.

### Verify Everything

Use **mail-tester.com**: send a test email to their address, then check your score. 9/10 or higher means your authentication is clean. Below 7/10 means something is broken.

---

## Domain Warmup

A brand new domain has no sending reputation. Email providers don't trust it. If you start sending 200 emails/day on day one, you will be flagged.

Warmup = building reputation gradually by sending low volumes and getting positive engagement.

### Warmup Schedule

| Week | Emails/Day | Focus |
|------|-----------|-------|
| 1 | 5-10 | Real conversations only — send to colleagues, get replies |
| 2 | 20-30 | Small cold outreach batches — highly targeted, good lists |
| 3 | 40-60 | Expand slightly — maintain >30% open rate |
| 4 | 80-100 | Normal volume — watch bounce and spam complaint rates |
| 5+ | Up to 200 | Full volume — monitor daily |

**Warning signs that warmup is failing:**
- Open rate drops below 20%
- Bounce rate above 3%
- Spam complaint rate above 0.1%
- Emails landing in Gmail Promotions tab

**Manual warmup vs tools:** Tools like Lemwarm, Warmup Inbox, or Mailreach automate warmup by sending emails to a network of inboxes that automatically open and engage. These help build reputation faster. They're worth it for new domains.

---

## List Quality

Sending to bad email addresses destroys your sender reputation. Every hard bounce tells inbox providers your list is dirty.

### Before Sending

1. **Verify email addresses** — Use a verification tool (NeverBounce, ZeroBounce, Hunter's verify, etc.) before importing any list. Remove invalid, catch-all, and risky emails.

2. **Target bounce rate:** Keep it below 2%. Above 5% is dangerous territory.

3. **Remove catch-all domains carefully** — Catch-all domains accept any email regardless of whether the mailbox exists. Your emails won't hard-bounce, but they may go nowhere.

4. **Never buy lists** — Purchased lists are old, dirty, unverified, and frequently include spam traps (addresses placed by inbox providers to catch spammers). One spam trap hit can blacklist your domain.

### Ongoing Hygiene

- Remove anyone who hasn't opened in 90 days from your sequence (move to a re-engagement campaign or suppress)
- Remove unsubscribes immediately — required legally and good for reputation
- Remove bounces from all future sends automatically

---

## Content That Hurts Deliverability

Spam filters evaluate content alongside authentication and reputation. These patterns trigger filters:

### Spam Trigger Words to Avoid

High-risk words and phrases (use sparingly or avoid):
- "Free" (especially in subject lines)
- "Guaranteed" / "100% guaranteed"
- "No obligation"
- "Act now" / "Limited time"
- "Congratulations"
- "You've been selected"
- "Click here"
- "Earn money" / "Make money"
- "Risk-free"
- "Special offer"
- Excessive exclamation points!!!
- ALL CAPS words

These don't automatically spam-filter you, but they're additive — the more of them in a single email, the higher the spam score.

### Content Rules

| Do | Don't |
|----|-------|
| Plain text or minimal HTML | Heavy HTML with complex tables, images |
| One link max per email | 5+ links — looks like phishing or newsletter |
| Personalized subject lines | Batch-blasted "LAST CHANCE" subject lines |
| Unsubscribe link | No unsubscribe mechanism |
| Consistent from name | Rotating from names |
| Short emails | Wall-of-text emails |

### The HTML Question

Plain text emails consistently get better deliverability than HTML emails for cold outreach. They look like real emails from real people — because they are.

If you need to include your company logo and a fancy template: don't. Save that for newsletters to opted-in subscribers. Cold email = plain text, signed like a person.

---

## Sending Limits by Platform

| Platform | Safe Daily Volume | Notes |
|----------|------------------|-------|
| Google Workspace (paid) | 500/day | Shared across all outgoing |
| Google Workspace + Warmup | Up to 2000/day | After full warmup |
| Microsoft 365 | 10,000/day | Generous, but still subject to reputation |
| SendGrid | Depends on plan | IP reputation matters at scale |
| Mailgun | Depends on plan | Good for transactional, OK for cold |
| Lemlist / Instantly / Apollo | Platform-managed | Warmup built in, use their sending infrastructure |

For cold outreach at scale (>500/day), dedicated sending platforms are better than Google/Microsoft direct — they're designed to manage reputation across many users.

---

## Checking Your Reputation

If you suspect deliverability problems, check these:

1. **Mail-tester.com** — Authentication and content score (10/10 is perfect)
2. **MXToolbox Blacklist Check** — Check if your domain or IP is on any blacklists
3. **Google Postmaster Tools** — Shows your domain reputation with Gmail (spam rate, auth failures)
4. **Microsoft SNDS** — Similar to Google Postmaster for Outlook/Hotmail

**If you're on a blacklist:**
- Stop sending immediately from that domain
- Identify the cause (bad list, spam complaints, warmup failure)
- Follow the blacklist's delisting process (each has its own)
- Consider using a new domain while the old one recovers

---

## Legal Requirements

Cold email has legal requirements in most markets. Breaking them isn't just unethical — it's fined.

| Regulation | Where | Key Requirements |
|-----------|-------|-----------------|
| CAN-SPAM | USA | Honest subject line, physical address, unsubscribe mechanism |
| CASL | Canada | Requires express or implied consent — much stricter than CAN-SPAM |
| GDPR | EU/EEA | Legitimate interest basis required; no soft opt-in |
| PECR | UK | Similar to GDPR; ICO enforcement |

**Minimum compliance for most cold email:**
- Include your company name and physical address in every email
- Provide a working unsubscribe link or reply-to-unsubscribe instruction
- Honor unsubscribes within 10 business days (CAN-SPAM) or immediately (GDPR best practice)
- Don't use misleading subject lines or from names

**Disclaimer:** This is practical guidance, not legal advice. For EU/Canada outreach, consult a lawyer who specializes in email marketing law — GDPR and CASL are stricter than most people realize.
