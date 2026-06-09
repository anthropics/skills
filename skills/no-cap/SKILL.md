---
name: no-cap
description: Turn your X bookmarks into actionable signals, filtering out the noise
user_invocable: true
---

# /no-cap

Extract signal from noise. Pulls your recent X/Twitter bookmarks, filters out marketing/spam/engagement bait, and extracts actionable intelligence. Dual output: structured markdown for agents, HTML email digest for humans.

## Commands

- `/no-cap` — Process new bookmarks (main loop)
- `/no-cap setup` — Configure ingestion method, auth, output directory
- `/no-cap auto-login` — Extract X cookies from Chrome (recommended, one-time)
- `/no-cap status` — Show stats and last run info
- `/no-cap update-cookies` — Update X session cookies when they expire (without re-running full setup)

## Setup Flow (`/no-cap setup`)

Guide the user through configuration:

1. **Sign into X** — Detect the user's platform and guide accordingly:

   **macOS users** — Run the auto-login command:
   ```bash
   cd {repoPath} && npx tsx src/cli.ts auto-login
   ```
   This extracts X cookies from Chrome automatically. macOS will prompt for Keychain access — click Allow.

   **Windows / Linux users** — Auto-login is macOS only. Guide them through the manual method:
   1. Open Chrome → go to x.com
   2. Press F12 (DevTools) → Application tab → Cookies → `https://x.com`
   3. Copy the values for `auth_token` and `ct0`
   4. Run:
   ```bash
   cd {repoPath} && npx tsx src/cli.ts update-cookies <auth_token> <ct0>
   ```
   Note: cookies expire roughly every 30 days. When the user sees an auth error, guide them to repeat these steps.

2. **Output directory** — Ask where to save signals (default: `~/no-cap-signals/`)

3. **Interests & sections** — Ask: "What topics or projects are you tracking? These become sections in your digest."
   - Let the user list topics freeform (e.g., "AI agents", "fine-tuning LLMs", "marketing", "Claude Code")
   - Also ask if they have active projects they want signals routed to (e.g., "my-app — AI dashboard", "trading bot")
   - Save these as `interests` and `projects` arrays in config
   - These guide how signals get categorized and routed — they're not hard filters, just lenses

4. **Email digest** — Ask if they want an HTML email digest after each run. If yes:
   - Ask for their email address
   - Ask for their Resend API key (free at https://resend.com — 100 emails/day on free tier)
   - No MCP plugins or heavy dependencies needed

5. Write config to `~/.no-cap/config.json` using the Write tool. **Set file permissions to 600** (owner-only read/write) since it contains session credentials. Make sure `repoPath` is set in the config to the directory where no-cap is installed.

6. **Test run** — Do a test fetch to verify credentials work:
   ```bash
   cd {repoPath} && npx tsx src/cli.ts fetch
   ```
   Where `{repoPath}` is the `repoPath` field from `~/.no-cap/config.json`.
   If it errors on auth, guide the user to re-check their cookies.

## Main Loop (`/no-cap`)

First, read the no-cap config to get the repo path:
- Read `~/.no-cap/config.json` and extract the `repoPath` field
- Use this path in all CLI commands below (shown as `{repoPath}`)

### Step 1: Fetch new bookmarks

Run the CLI to get new bookmarks:
```bash
cd {repoPath} && npx tsx src/cli.ts fetch
```

This returns JSON with new bookmarks (already diffed against state). If "No new bookmarks" — tell the user and stop.

### Step 2: Noise Filter (3 layers)

For each bookmark, evaluate through three layers. Be aggressive — most content is noise.

**Layer 1 — Account-level:**
- Is this a marketing/promo account? (constant CTAs, course selling, affiliate patterns)
- Is the author repeating the same pitch across multiple bookmarks?
- Did the account recently pivot to whatever's trending? (carpet-bagging)
- Output: PASS or FILTERED with reason

**Layer 2 — Post-level:**
- Contains affiliate/referral links? → NOISE
- "Link in bio" / "DM me for" patterns? → NOISE
- Engagement bait structure? (rage bait, false urgency, vague boasts) → NOISE
- Is this an ad or sponsored content? → NOISE
- Is this just a meme or joke with no insight? → NOISE (unless genuinely clever insight underneath)
- **Bare link to an X article (`x.com/i/article/...`)?** The link-follower now automatically fetches article title + preview text via the X API. If the bookmark text starts with `[Article: ...]`, the article content was successfully enriched — evaluate it through the normal noise filter using that content. If enrichment failed and the text is still just a bare URL, pass it through as a `learning` signal with the article link so the user can click through — do NOT auto-filter it as noise.
- Output: PASS or FILTERED with reason

**Layer 3 — Content-level:**
- Is there an extractable idea, technique, pattern, or insight?
- Is it novel, or common knowledge repackaged?
- Is it specific (concrete details, examples, code) or vague platitudes?
- Would this change how someone builds, thinks, or decides?
- Strong opinions from indie creators with genuine experience ARE signal — don't filter opinions that come from real expertise
- Output: PASS (with signal preview) or FILTERED with reason

**Important: Signal-in-the-noise.** A post can be mostly noise but still contain a real idea buried inside the hype. For example, a Polymarket trading post might be 80% marketing fluff but contain a genuinely novel arbitrage mechanism. A course seller might drop a real technique in their pitch thread. When you filter a post as noise, always check: **is there a kernel worth extracting?** If yes, classify it as `partial_signal` — extract the idea but note what's noise around it. These go in a separate "Signal in the Noise" section, not the main signals.

### Step 3: Classify bookmark intent

Before extracting signals, classify WHY the user bookmarked this. People bookmark for different reasons:

| Intent | Description | Example |
|--------|-------------|---------|
| **signal** | Contains an actionable insight, technique, or pattern | "MCTS for agent decision-making replaces brute-force loops" |
| **action_item** | Something the user should DO — a course, exam, event, tool to try, tutorial to follow | "Claude Code architect certification exam is now open" |
| **project_signal** | Relevant to a specific project the user is working on (check config `projects`) | A post about WASM sandboxing when user has an agent platform project |
| **learning** | Educational content worth saving for reference — deep dives, papers, threads | "Comprehensive thread on transformer architecture internals" |
| **tool** | A tool, library, or resource worth bookmarking | "New CLI tool for X/Twitter data export" |

**Do NOT filter out action items as noise.** A post about "how to pass the Claude Code architect exam" is not marketing — it's something the user wants to be reminded to do. Same for events, courses, tutorials, deadlines.

### Step 4: Extract signals and action items

For each bookmark that passed noise filtering, extract based on its intent:

**For signals and project_signals:**
```
Title: One-sentence summary of the core idea
Type: technical_insight | market_signal | workflow | tool | trend | opinion
Intent: signal | project_signal
Project: [which project, if project_signal — match against config projects]
Actionability: immediate | near_term | reference
Tags: [freeform topic tags — try to match user's configured interests]
Source: @handle, URL, date
Context: Why this matters — 2-3 sentences. Strip narrative, isolate the mechanism.
```

**For action items:**
```
Title: What to do — imperative form ("Take Claude Code architect exam", "Try Resend for email")
Intent: action_item
Priority: high | medium | low
Source: @handle, URL, date
Context: Why this is worth doing — 1-2 sentences
```

**For learning resources:**
```
Title: What this teaches
Intent: learning
Tags: [topic tags]
Source: @handle, URL, date
Context: What you'll learn — 1-2 sentences
```

If the bookmark has a quoted tweet or linked post (from link propagation), include that context in the analysis.

### Step 5: Write agent output

**Session file** — Write to `{signalDir}/{YYYY-MM-DD}/session-{N}.md`:

```markdown
# YYYY-MM-DD — Session N

## Signals

**[Theme Name]**
- [Signal 1] — [2-3 sentence context with the mechanism, why it matters, and source] (@handle)
- [Signal 2] — [context] (@handle, @handle2)

**[Theme Name 2]**
- [Signal] — [context] (@handle)

## Project Signals
[Only if user has projects configured]

**[Project Name]:**
- [Signal] — [why it matters for this project] (@handle)

## Action Items
- [ ] [What to do] — [brief context] (@handle) — Priority: high/medium/low

## Signal in the Noise
- [Extracted idea] — [context]. Source is noisy because [reason]. (@handle)

## Noise
- [What the post was about] — Filtered because: [specific reason] (@handle)

## Stats
- Processed: X | Signals: Y | Actions: Z | Noise: N
```

Determine session number by counting existing session files in today's directory.

**Master file** — Read `{signalDir}/MASTER.md`, then rewrite to reflect cumulative state. This file is YOUR primary reference — write it so you (Claude) can load it next session and immediately understand what's happening, what matters, and what to do.

**Structure:**

```markdown
# No Cap — Signal Master

_Last updated: YYYY-MM-DD_
_Sessions: N total | Latest: YYYY-MM-DD_

## New Since Last Session
[Quick diff — what changed this run. 2-3 sentences max. Remove this section when the next session runs.]

## Project Signals
[Grouped by the user's configured projects. Each signal has enough context to act on without reading the source.]

### [Project Name]

**[Signal title]**
[2-3 sentences: what it is, why it matters for this project, what the mechanism/technique is. Include enough detail that you could reason about it or suggest actions without going back to the tweet.]
Source: @handle · YYYY-MM-DD · actionability
Connects to: [what existing project work this relates to]

### Unrouted
[Signals that don't map to any configured project but are still actionable]

## Action Items
- [ ] [Action] — [context] (source, date) — Priority: high/medium/low

## Noise Patterns
[Recurring noise patterns across sessions — accounts/topics to auto-filter. This section compounds over time.]
- @handle — [pattern] (seen N times)

## Historical
[Signals that have been acted on or are >30 days stale. Compressed to one-liners.]
```

**Writing principles for MASTER.md:**
- **Write for yourself (Claude).** This is agent context, not human docs. Include the mechanism, not just the name.
- **Map to projects first, topics second.** The user configured their projects for a reason — route signals there.
- **Include enough detail to act.** "FlashCompact exists" is useless. "FlashCompact: purpose-built context compaction model, 33K tok/s, 200K→50K in 1.5s, not the usual LLM+vectorDB pattern — relevant to No Cap's context window problem" is actionable.
- **Compound noise patterns.** If @IndieGameJoe shows up as noise 3 sessions in a row, note the pattern so future runs auto-filter.
- **Keep it under 200 lines.** Compress old signals to historical when they're stale or acted on.

### Step 6: Generate and send email digest (if configured)

Generate the email digest HTML using the EXACT template structure below. Do NOT improvise the layout — use this template and fill in the content. The template has been tested across email clients and renders correctly.

**How to use the template:**
1. Copy the template below
2. Replace `{date}`, `{theme_count}`, `{action_count}` in the header
3. Replace `{tldr}` with 2-3 sentence TL;DR
4. For each action item: copy the action card block, fill in icon emoji, title, description, and source link
5. For each signal theme: copy the signal card block, fill in icon emoji, heading, prose paragraph, and source handles
6. For secondary/reference signals (lower priority): use the two-column card block
7. For project signals (if configured): use the project card block
8. For noise: fill in the noise entries
9. Write the completed HTML to `{signalDir}/{YYYY-MM-DD}/digest-{N}.html`

**IMPORTANT:** Use `valign="top"` on all icon `<td>` elements. Set icon `<div>` with `text-align:center;line-height:36px` (or 40px for signal icons). This keeps icons centered in their squares.

````html
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>No Cap — {date}</title>
  <link href="https://fonts.googleapis.com/css2?family=Instrument+Serif:ital@0;1&family=DM+Sans:wght@400;500;600;700&display=swap" rel="stylesheet">
</head>
<body style="margin:0;padding:0;background-color:#ffffff;font-family:'DM Sans',Helvetica,Arial,sans-serif;-webkit-font-smoothing:antialiased;">
<table role="presentation" width="100%" cellpadding="0" cellspacing="0" border="0" style="background-color:#ffffff;">
<tr><td align="center" style="padding:0;">
<table role="presentation" width="640" cellpadding="0" cellspacing="0" border="0" style="max-width:640px;width:100%;">

  <!-- HEADER -->
  <tr><td style="background-color:#faf9f5;padding:40px 36px 24px;">
    <table role="presentation" width="100%" cellpadding="0" cellspacing="0" border="0">
      <tr>
        <td>
          <p style="margin:0;font-family:'Instrument Serif',Georgia,serif;font-size:28px;font-weight:400;color:#262624;letter-spacing:-0.01em;">no cap</p>
          <p style="margin:4px 0 0;font-size:12px;color:#87867f;">Signal from noise &middot; {date}</p>
        </td>
        <td style="text-align:right;vertical-align:top;">
          <p style="margin:0;font-size:12px;color:#87867f;">{theme_count} themes &middot; {action_count} actions</p>
        </td>
      </tr>
    </table>
  </td></tr>

  <!-- TL;DR -->
  <tr><td style="background-color:#faf9f5;padding:8px 36px 32px;">
    <p style="margin:0;font-family:'Instrument Serif',Georgia,serif;font-size:19px;font-style:italic;color:#4a4540;line-height:1.55;">{tldr}</p>
  </td></tr>

  <!-- DIVIDER -->
  <tr><td style="background-color:#faf9f5;padding:0 36px;"><div style="height:1px;background:#e5e0db;"></div></td></tr>

  <!-- TO DO SECTION HEADER -->
  <tr><td style="background-color:#faf9f5;padding:28px 36px 16px;">
    <p style="margin:0;font-size:11px;font-weight:700;color:#262624;text-transform:uppercase;letter-spacing:0.12em;">To Do</p>
  </td></tr>

  <!-- ACTION CARD (repeat for each action item) -->
  <tr><td style="background-color:#faf9f5;padding:0 36px 10px;">
    <table role="presentation" width="100%" cellpadding="0" cellspacing="0" border="0" style="background:#f0eee6;border-radius:16px;">
      <tr>
        <td width="56" valign="top" style="padding:20px 0 20px 20px;">
          <div style="width:36px;height:36px;background:#d97757;border-radius:10px;text-align:center;line-height:36px;">
            <span style="color:#ffffff;font-size:18px;">{action_icon}</span>
          </div>
        </td>
        <td style="padding:20px 24px 20px 12px;">
          <p style="margin:0 0 4px;font-size:14px;font-weight:600;color:#262624;">{action_title}</p>
          <p style="margin:0;font-size:13px;color:#6b6157;line-height:1.5;">{action_description} — <a href="{action_url}" style="color:#87867f;text-decoration:underline;">{action_source}</a></p>
        </td>
      </tr>
    </table>
  </td></tr>
  <!-- END ACTION CARD -->

  <!-- SPACER before signals -->
  <tr><td style="background-color:#faf9f5;height:24px;"></td></tr>

  <!-- SIGNALS SECTION HEADER -->
  <tr><td style="background-color:#f0eee6;padding:28px 36px 20px;">
    <p style="margin:0;font-family:'Instrument Serif',Georgia,serif;font-size:24px;font-weight:400;color:#262624;">Signals</p>
  </td></tr>

  <!-- SIGNAL CARD (repeat for each primary signal theme) -->
  <tr><td style="background-color:#f0eee6;padding:0 36px 12px;">
    <table role="presentation" width="100%" cellpadding="0" cellspacing="0" border="0" style="background:#faf9f5;border-radius:16px;">
      <tr>
        <td width="56" valign="top" style="padding:24px 0 24px 20px;">
          <div style="width:40px;height:40px;background:#262624;border-radius:12px;text-align:center;line-height:40px;">
            <span style="color:#faf9f5;font-size:20px;">{signal_icon}</span>
          </div>
        </td>
        <td style="padding:24px 24px 24px 14px;">
          <p style="margin:0 0 6px;font-family:'Instrument Serif',Georgia,serif;font-size:17px;font-weight:400;color:#262624;line-height:1.3;">{signal_heading}</p>
          <p style="margin:0 0 10px;font-size:13px;color:#6b6157;line-height:1.6;">{signal_prose}</p>
          <p style="margin:0;font-size:12px;color:#b0aea5;">{signal_sources}</p>
        </td>
      </tr>
    </table>
  </td></tr>
  <!-- END SIGNAL CARD -->

  <!-- TWO-COLUMN CARDS (for secondary/reference signals, optional) -->
  <tr><td style="background-color:#f0eee6;padding:0 36px 12px;">
    <table role="presentation" width="100%" cellpadding="0" cellspacing="0" border="0">
      <tr>
        <td width="50%" valign="top" style="padding-right:6px;">
          <table role="presentation" width="100%" cellpadding="0" cellspacing="0" border="0" style="background:#faf9f5;border-radius:16px;">
            <tr><td style="padding:20px;">
              <div style="width:36px;height:36px;background:#262624;border-radius:10px;text-align:center;line-height:36px;margin-bottom:12px;">
                <span style="color:#faf9f5;font-size:16px;">{col1_icon}</span>
              </div>
              <p style="margin:0 0 6px;font-family:'Instrument Serif',Georgia,serif;font-size:16px;color:#262624;">{col1_heading}</p>
              <p style="margin:0 0 8px;font-size:12px;color:#6b6157;line-height:1.5;">{col1_prose}</p>
              <p style="margin:0;font-size:11px;color:#b0aea5;">{col1_note}</p>
            </td></tr>
          </table>
        </td>
        <td width="50%" valign="top" style="padding-left:6px;">
          <table role="presentation" width="100%" cellpadding="0" cellspacing="0" border="0" style="background:#faf9f5;border-radius:16px;">
            <tr><td style="padding:20px;">
              <div style="width:36px;height:36px;background:#262624;border-radius:10px;text-align:center;line-height:36px;margin-bottom:12px;">
                <span style="color:#faf9f5;font-size:16px;">{col2_icon}</span>
              </div>
              <p style="margin:0 0 6px;font-family:'Instrument Serif',Georgia,serif;font-size:16px;color:#262624;">{col2_heading}</p>
              <p style="margin:0 0 8px;font-size:12px;color:#6b6157;line-height:1.5;">{col2_prose}</p>
              <p style="margin:0;font-size:11px;color:#b0aea5;">{col2_note}</p>
            </td></tr>
          </table>
        </td>
      </tr>
    </table>
  </td></tr>
  <!-- END TWO-COLUMN CARDS -->

  <!-- PROJECT CARD (only if user has projects configured, repeat per project) -->
  <tr><td style="background-color:#f0eee6;padding:0 36px 12px;">
    <table role="presentation" width="100%" cellpadding="0" cellspacing="0" border="0" style="background:#faf9f5;border:1px solid #d97757;border-radius:16px;">
      <tr>
        <td width="56" valign="top" style="padding:20px 0 20px 20px;">
          <div style="width:36px;height:36px;background:#d97757;border-radius:10px;text-align:center;line-height:36px;">
            <span style="color:#ffffff;font-size:16px;">{project_icon}</span>
          </div>
        </td>
        <td style="padding:20px 24px 20px 12px;">
          <p style="margin:0 0 2px;font-size:10px;font-weight:700;color:#d97757;text-transform:uppercase;letter-spacing:0.1em;">{project_name}</p>
          <p style="margin:0;font-size:13px;color:#6b6157;line-height:1.5;">{project_signals_prose}</p>
        </td>
      </tr>
    </table>
  </td></tr>
  <!-- END PROJECT CARD -->

  <!-- NOISE SECTION -->
  <tr><td style="background-color:#f0eee6;padding:12px 36px 32px;">
    <p style="margin:0 0 8px;font-size:10px;font-weight:700;color:#b0aea5;text-transform:uppercase;letter-spacing:0.12em;">Filtered &middot; {noise_count}</p>
    <!-- Repeat for each noise entry: -->
    <p style="margin:0 0 3px;font-size:12px;color:#b0aea5;">{noise_entry}</p>
  </td></tr>

  <!-- DARK FOOTER -->
  <tr><td style="background-color:#141413;padding:32px 36px;">
    <table role="presentation" width="100%" cellpadding="0" cellspacing="0" border="0">
      <tr>
        <td>
          <p style="margin:0;font-family:'Instrument Serif',Georgia,serif;font-size:18px;color:#faf9f5;">no cap</p>
          <p style="margin:6px 0 0;font-size:12px;color:#87867f;">Signal from noise &middot; Built with Claude Code</p>
        </td>
        <td style="text-align:right;vertical-align:top;">
          <p style="margin:0;font-size:12px;color:#87867f;">Powered by No Cap skill</p>
        </td>
      </tr>
    </table>
  </td></tr>

</table>
</td></tr>
</table>
</body>
</html>
````

**Rules for using the template:**
- Do NOT change any styles, padding, colors, or border-radius values
- Do NOT invent new card layouts or section types — use only the blocks above
- Omit sections that don't apply (e.g., skip To Do if no action items, skip Project Card if no projects)
- For the two-column layout: only use when you have exactly 2 secondary/reference signals. Otherwise use full-width signal cards.
- Pick a relevant emoji for each icon. Keep it simple — one emoji per icon square.
- Noise entries should say what the post was about AND why it was filtered.
- **EVERY @handle in the ENTIRE email MUST be a clickable link to the original tweet.** This applies to ALL sections: action cards, signal cards, two-column cards, project cards, noise entries — no exceptions. Use `<a href="{tweet_url}" style="color:#b0aea5;text-decoration:underline;">@handle</a>` for signal/noise source lines and `<a href="{tweet_url}" style="color:#87867f;text-decoration:underline;">@handle</a>` for action card sources. For quoted tweet authors, link to the quoted tweet URL. The tweet URL comes from the bookmark data (`url` field, or `quotedTweet.url` for QT authors) — never link to just the profile page. Plain text `@handle` with no `<a>` tag is a bug.

Save the HTML to `{signalDir}/{YYYY-MM-DD}/digest-{N}.html`.

If email is configured, send it:
```bash
cd {repoPath} && npx tsx src/cli.ts send-email "No Cap — {N} signals from {date}" "{signalDir}/{YYYY-MM-DD}/digest-{N}.html"
```

**First run only** (no `{signalDir}/state.json` existed before this run): After sending the email, print this warning:

```
⚠️  FIRST-RUN NOTICE: CHECK YOUR SPAM FOLDER
Emails from No Cap are sent via Resend (from onboarding@resend.dev).
Your email provider may flag the first one as spam.
If you don't see it in your inbox, check spam/junk and mark it as "Not Spam"
so future digests land in your inbox.
```

### Step 7: Update state

After successful processing, mark the newest bookmark as processed:
```bash
cd {repoPath} && npx tsx src/cli.ts mark-done {newestBookmarkId}
```

### Step 8: Print summary

After processing, print:
```
No Cap — {date}
Processed: {X} bookmarks
Signals: {Y} | Action items: {Z} | Learning: {W}
Noise filtered: {N}
Saved to: {signalDir}/{date}/session-{N}.md
Master updated: {signalDir}/MASTER.md
{Email sent to: address | Email digest saved to: path}
```

## Status (`/no-cap status`)

```bash
cd {repoPath} && npx tsx src/cli.ts status
```

Show the output to the user.

## Update Cookies (`/no-cap update-cookies`)

When the user's X cookies expire (usually every ~30 days), they'll see an auth error. Instead of re-running full setup:

1. Guide them to get fresh cookies: open X in browser → Dev Tools (F12) → Application → Cookies → `x.com` → copy `auth_token` and `ct0`
2. Run the update command:
```bash
cd {repoPath} && npx tsx src/cli.ts update-cookies <auth_token> <ct0>
```
3. The command updates the config and runs a test fetch to verify.

This preserves all other settings (output dir, interests, email config).

## Troubleshooting

**"Not logged into X" or "Missing auth_token"**
- Run: `cd {repoPath} && npx tsx src/cli.ts auto-login`
- macOS will prompt for Keychain access — click Allow
- If auto-login fails, manually copy cookies from Chrome DevTools and run `update-cookies`

**"X API returned 400" or "X authentication failed"**
- The CLI auto-retries with fresh query IDs on 400/404 errors
- If it still fails, run: `cd {repoPath} && npx tsx src/cli.ts discover`
- If discover doesn't help, cookies may be expired — run `/no-cap update-cookies`

**"No new bookmarks" when you know you have new ones**
- The high-water mark may be set to a bookmark you deleted
- Fix: delete `{signalDir}/state.json` to reset, then run `/no-cap` again

## Principles

- **Assume noise until proven signal.** Most bookmarked content is still mostly noise.
- **Strong opinions from practitioners are signal.** An indie dev with real experience sharing a genuine opinion — even a hot take — is not noise. Marketing is noise.
- **Not everything is a signal — some things are action items.** "Take this exam", "try this tool", "attend this event" are not signals to extract — they're things to DO. Classify them as action items with clear next steps.
- **Extract the mechanism, not the story.** Strip narrative, isolate what's actually useful.
- **Use configured interests as lenses, not filters.** The user's topics and projects guide categorization, but don't filter out things that don't match — unexpected signals are often the most valuable.
- **Route, don't hoard.** Every signal should end up somewhere useful — a project, an action item, or a learning resource.
