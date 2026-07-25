# DRAFTS ONLY — The Never-Send Safety Discipline

This reference answers exactly one decision: **why is "drafts only — never send" the non-negotiable safety property, and how is it enforced?**

## The Core Rule

> **The skill creates drafts. It NEVER sends.**

This is not a soft preference. It is the safety property that makes the skill safe to run automatically on a recurring schedule. Without it, the skill could send a wrong reply at 6 AM to the wrong person about the wrong topic — and the user discovers it hours later when it's already been read.

The discipline is enforced at three layers:

1. **In the skill body** — stated multiple times in `SKILL.md`, in `cs-inbox-triage.md` (agent), and in `/cs:inbox-triage` (command)
2. **In the draft mechanics** — every draft creation explicitly uses the "draft" verb of the email tool (Gmail's `drafts.create`, Outlook's `Messages.SaveAsDraft`, etc.) — never `send`, `transmit`, `dispatch`
3. **In the post-run validator** — `scripts/draft_safety_validator.py` scans the action log for any send-shaped tool call and FAILs the run if detected

## Why This Property Is Non-Negotiable

Email is one of the highest-blast-radius surfaces a tool can touch:

- **Reversibility:** sending an email is irreversible (you can recall in Gmail/Outlook within a narrow window, but the recipient may have already read it)
- **Visibility:** the recipient sees it instantly; PR risk for famous-sender mistakes
- **Trust:** users who can't trust the tool to not auto-send will not run it on a schedule, which defeats the design
- **Surprise:** unlike auto-replying with an obvious AI signature, the skill matches user voice — the recipient won't realize it was automated

A skill that **drafts** can be reviewed before sending. A skill that **sends** has no review surface. The asymmetry between "low cost of draft + user review" vs "high cost of bad send" makes the choice obvious: only draft.

## How to Tell Drafts From Sends in Tool Calls

Different email tools surface this differently:

| Tool | Draft verb | Send verb |
|---|---|---|
| Gmail (API / MCP) | `users.drafts.create` | `users.messages.send` |
| Outlook / Graph | `Messages.SaveAsDraft` / `me/messages` (POST) | `me/sendMail` / `me/messages/{id}/send` |
| IMAP | append to Drafts folder | not directly via IMAP; would use SMTP |
| Custom MCP | `email.draft.*` | `email.send.*` |

The pattern is consistent: drafts are saved to a server-side drafts folder; sends transit the wire to the recipient. The boundary is bright; the validator's job is to never cross it.

## What `draft_safety_validator.py` Does

The validator scans the per-run triage log (`triage-log/<date>-<label>.md`) for tool-call patterns matching send verbs:

- `send_email`, `send_mail`, `sendMail`, `send_message`
- `gmail.users.messages.send`, `users.messages.send`
- `outlook.send`, `graph.sendMail`, `me/sendMail`, `me/messages/.*?/send`
- Any verb literal `send` in a tool-call line (case-insensitive)

If any match: the validator returns FAIL with the matching line surfaced. The run is flagged. The user is alerted immediately. The skill author investigates.

The validator runs **post-flight** — after the skill has completed its 10 steps. It cannot prevent a bad send (that's the skill body's job, by avoiding the send tool entirely), but it can detect one if the skill body's discipline broke. Defense in depth.

## What Triage Does Instead Of Sending

For every reasonable reply candidate:

1. Create a draft in the original thread (`gmail.users.drafts.create` or equivalent)
2. Set `to`, `subject` (`Re: [original]`)
3. Body from `email-patterns.md` voice rules
4. Draft sits in user's drafts folder, ready for user review + send

The triage report then surfaces:
- Stats: `N drafts created (all in drafts folder for your review)`
- Detailed cards: sender / subject / category / recommendation — but **NO draft text previews** (the drafts are already in the email client; previewing them in the report is duplication and confuses "draft created" with "draft sent")

## Edge Cases

### "I want the skill to send"

Don't. The skill is designed to not send. If the user wants automated send, that's a different skill with a different safety posture (likely much narrower scope — only sends in response to a specific webhook with specific approval state, etc.). Mixing autonomous-send with autonomous-classification is a bad combination.

### "But the user already approved this offer"

Approval at setup time is not approval at draft time. The user approves the FRAMEWORK (TAKE-IT signals, PASS signals) at setup. The user approves the actual sending of a specific reply at review time. These are different approvals.

### "What about scheduled sends?"

Scheduled send (e.g., "draft now, send in 2 hours") is still a send. The validator catches it. If the user wants to schedule a send, the user does it manually after reviewing the draft.

### "What if I'm sure the draft is right?"

Cool — open the draft, click send. The skill doesn't need to do it for you.

## How To Verify The Discipline Holds

After any triage run:

```bash
python ../scripts/draft_safety_validator.py \
  --action-log ${WORKSPACE}/Email/triage-log/$(date +%Y-%m-%d)-*.md
```

If output is `PASS` (no send verbs detected): discipline held.
If output is `FAIL` with surfaced lines: discipline broke; investigate.

The validator can also be run in CI / on a cron schedule against the latest triage log to detect drift over time.

## Anti-Patterns

- Adding a "send" option to the skill body "for convenience"
- Bypassing the validator "for one trusted reply"
- Letting the user say "just send it" in chat and acting on it
- Catching a send action in the validator and shrugging it off
- Pretending "save draft and queue for send in 30 min" is meaningfully different from send

## Citations

The drafts-only safety discipline draws on:

1. **Schneier, *Beyond Fear* (Springer, 2003)** — security-by-design vs security-by-policy. The drafts-only rule is security by design (the skill cannot send) vs by policy (the user is asked to please not send) — the former is much stronger.

2. **Allspaw & Robbins, *Web Operations* (O'Reilly, 2010), Chapter 3** — blast radius reasoning. Email is a high-blast-radius surface; the cost of mistakes is high relative to the cost of inconvenience-by-design.

3. **Google SRE Workbook — Chapter 16, "Canarying Releases".** Canarying applies to email automation: send a draft first (canary), let the user review (signal), then promote (user clicks send). The triage skill IS the canary half.

4. **NTSB / Air Traffic Control "two-person rule" doctrine.** High-stakes actions require two-person authorization. Triage's draft + user-review-and-send pattern is the same doctrine: skill drafts, user authorizes, action occurs.

5. **Atul Gawande, *Checklist Manifesto*** — the "kill switch" pattern. Drafts-only is a kill switch built into the skill's architecture, not a configurable preference.

6. **Marc Andreessen, "Why Software Is Eating the World"** — but with an asterisk: software that touches communication channels needs explicit safety properties because the failure modes are public.

7. **Bruce Schneier, *Click Here to Kill Everybody* (Norton, 2018)** — the IoT-era principle that automation should never act in ways the user can't undo. Drafts can be deleted; sends cannot.
