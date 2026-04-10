---
name: synthesis-slack-sync
description: "Slack channel sync protocol for AI-assisted workflows. Reads channels and threads via Slack MCP, saves to local transcript files, and updates daily action plans. Handles mid-day re-syncs with thread staleness detection. Use when asked to: slack sync, sync from slack, check slack, read channels, sync messages, sync transcripts, what's new on slack."
license: "CC0-1.0"
metadata:
  depends_on: "synthesis-daily-rituals, synthesis-project-management"
  author: "Rajiv Pant"
  version: "1.2.0"
  source_repo: "github.com/rajivpant/synthesis-skills"
  source_type: "public"
---

# Synthesis Slack Sync

A protocol for syncing Slack channels and threads to local transcript files using Slack MCP. Designed for AI-assisted workflows where an agent reads Slack on behalf of a user, saves transcripts locally, and updates a daily action plan.

This skill provides the **protocol** — the sync methodology, thread re-reading discipline, transcript format, and action plan update rules. A per-project **config file** (`.claude/slack-sync.yaml`) provides the specifics: which channels, which paths, which DMs.

## Configuration

Create `.claude/slack-sync.yaml` in each project that uses this skill:

```yaml
# .claude/slack-sync.yaml — Slack sync configuration
#
# workspace: (REQUIRED) Workspace identifier. Determines transcript subdirectory structure:
#   {transcripts_path}/{workspace}/channels/YYYY-MM-DD.md
#   {transcripts_path}/{workspace}/dms/YYYY-MM-DD.md
#   {transcripts_path}/{workspace}/group-dms/YYYY-MM-DD.md
# channels: Slack channels to monitor. All channel types supported.
# dm_channels: Active 1:1 DM conversations to check (optional).
# group_dm_channels: Group DM (mpim) conversations to check (optional).
# transcripts_path: Root directory for transcripts (relative to ai-knowledge repo root).
# action_plan_path: Where daily action plans live (relative to ai-knowledge repo root).
# ai_knowledge_repo: Absolute path to the ai-knowledge repo where transcripts are stored.

ai_knowledge_repo: ~/projects/ai-knowledge

workspace: example-workspace

transcripts_path: projects/_transcripts/
action_plan_path: projects/_daily-plans/

channels:
  - id: C0EXAMPLE01
    name: team-general
    type: public_channel
  - id: C0EXAMPLE02
    name: eng-pull-requests
    type: private_channel
  # Add more channels as needed

dm_channels: []
  # - id: U0EXAMPLE01
  #   name: Jane Doe
  #   dm_id: D0EXAMPLE01

group_dm_channels: []
  # - id: C0EXAMPLE03
  #   name: "Project Alpha team"
```

If the config file is missing, the skill should warn and ask the user to create one.

---

## Prerequisites

- **Slack MCP must be connected and authenticated.** If any Slack tool call fails with an auth error, stop and instruct the user to re-authenticate: `claude mcp auth slack`, then restart the IDE/CLI.
- **Local transcript files must exist or be created.** The skill creates today's files as needed under `{workspace}/channels/`, `{workspace}/dms/`, and `{workspace}/group-dms/`.

---

## ⛔ NEVER Use Slack Search API for Lookups

**When verifying whether a message was sent, or looking up past conversations, ALWAYS read local transcript files first.** Use `Grep` on transcript files in the transcripts directory. NEVER call `slack_search_public`, `slack_search_public_and_private`, or `slack_read_channel` for historical lookups.

The Slack search API has indexing delays (recent messages don't appear), misses thread replies entirely, and is slower and more expensive than local file reads. On 2026-04-01, four Slack search API calls returned "no results" for messages that existed in threads — nearly causing duplicate messages to be sent.

**The only valid uses of the Slack MCP API are:**
1. Syncing NEW messages during this protocol (Steps 1-3)
2. Reading a specific thread by TS that was never synced locally

---

## Sync Protocol

Every sync — whether day-start, mid-day, or day-end — follows these steps. No shortcuts, no skipped steps.

### Step 0: Run the thread checker (MANDATORY)

Before doing anything else, run the thread checker script on each transcript file that exists for today:

```bash
python3 ~/.claude/skills/synthesis-slack-sync/thread_checker.py {transcripts_path}/{workspace}/channels/YYYY-MM-DD.md [action_plan_file]
python3 ~/.claude/skills/synthesis-slack-sync/thread_checker.py {transcripts_path}/{workspace}/dms/YYYY-MM-DD.md [action_plan_file]
python3 ~/.claude/skills/synthesis-slack-sync/thread_checker.py {transcripts_path}/{workspace}/group-dms/YYYY-MM-DD.md [action_plan_file]
```

Skip any file that does not yet exist (e.g., no DMs synced today). Combine the output from all runs into a single checklist. You MUST re-read every thread listed during Step 2. The script exists because manually deciding which threads to re-read has repeatedly failed — threads get skipped and messages get missed.

### Step 1: Read channels for new top-level messages

For each channel in the config:

```
slack_read_channel(channel_id, oldest=LAST_SYNC_TIMESTAMP, limit=30)
```

- On **first sync of the day** (no channels transcript file exists yet): omit `oldest` or use midnight timestamp.
- On **subsequent syncs**: use the timestamp of the last sync recorded in the channels transcript file.
- Note the **reply count** on every message that has threads. These will be re-read in Step 2.

### Step 2: Re-read ALL active threads — today AND recent days

**This is the most important step. It is the step that gets skipped and causes missed messages.**

Thread replies do NOT appear as channel-level messages. The only way to detect them — including the user's own replies — is to re-read threads. This step must cover three sources of active threads:

**Source A: Threads in today's transcripts.** For every message in today's channels, DMs, and group-DMs transcript files that shows a thread (reply count > 0), re-read the full thread.

**Source B: Threads from yesterday's transcripts that may have new replies.** Open the previous day's transcript files (`{workspace}/channels/`, `{workspace}/dms/`, `{workspace}/group-dms/` for yesterday's date). For every thread that was active (had replies), re-read it. This catches: overnight replies, the user's own replies to threads from yesterday, and continuing conversations that span days.

**Source C: Threads surfaced by Step 1.** Any message returned by Step 1 that shows "Thread: N replies" must be re-read, even if the parent message is from a previous day. Channel reads return messages in reverse chronological order — a thread from 3 days ago can appear in the channel read if it had recent activity.

```
slack_read_thread(channel_id, message_ts=PARENT_TS)
```

Rules:
- **Never use the `oldest` parameter on thread reads.** It causes missed replies. Read the full thread every time.
- **Compare the reply count and latest reply timestamp** against what's in the local transcript.
- **If new replies exist**, append them to the appropriate transcript file for today (channels, DMs, or group-DMs), even if the parent message is from a previous day.
- **If the user sent a message** in a thread, it does NOT appear as a new channel-level message. The only way to detect it is to re-read the thread. If this step is skipped, the action plan shows drafts as "unsent" when the user already sent them.

**Mechanical check:** Before reporting "no new messages" for any sync, verify that:
1. Every thread TS in today's transcripts was re-read and reply counts match.
2. Every active thread from yesterday's transcripts was re-read for new replies.
3. Every thread indicator from Step 1 channel reads was followed.

**Why Source B matters:** On 2026-03-31, the user replied to an engineer's thread from the previous night. The reply didn't appear as a channel-level message. Because the thread was from the previous day and not in today's transcript, the sync missed it entirely — the daily plan showed the draft as unsent when the user had already sent it.

### Step 3: Check DMs

For each DM channel in the config:

```
slack_read_channel(channel_id=DM_CHANNEL_ID, oldest=LAST_SYNC_TIMESTAMP, limit=20)
```

Only check DMs that have active conversations. Don't read every DM — the config file specifies which ones are active.

### Step 3b: Check Group DMs

For each group DM channel in the config:

```
slack_read_channel(channel_id=GROUP_DM_ID, oldest=LAST_SYNC_TIMESTAMP, limit=20)
```

Group DMs (multi-party IMs) are separate from 1:1 DMs. They use channel IDs, not user IDs. Only check group DMs listed in the config.

### Step 4: Save to local transcripts

**This step is not optional. Never skip it, even if "nothing changed."**

Write each message type to its own transcript file under the workspace directory:

- **Channels:** `{transcripts_path}/{workspace}/channels/YYYY-MM-DD.md` — channel messages and thread replies from Steps 1-2.
- **DMs:** `{transcripts_path}/{workspace}/dms/YYYY-MM-DD.md` — 1:1 DM messages from Step 3.
- **Group DMs:** `{transcripts_path}/{workspace}/group-dms/YYYY-MM-DD.md` — group DM messages from Step 3b.

For each file:
- Record the sync time (e.g., `## Mid-day sync (~14:30 EDT)`).
- If the file doesn't exist, create it with the standard header and create directories as needed.
- If no messages of that type were found, skip that file (do not create empty files).

Meeting transcripts are NOT part of Slack sync — they are handled by the daily-rituals skill and placed in `{transcripts_path}/{workspace}/meetings/`.

### Step 5: Update action plan

- **Mark sent messages as SENT** with timestamps. Cross-reference messages the user sent against draft messages in the action plan.
- **Update waiting-on-others** table with any new information from thread replies.
- **Note new action items** or signals worth responding to in the "Things to Know" section.
- **Draft replies with grounding research.** When a Slack message requires a response (technical question, status request, bug report), research the answer in primary sources (source code, config files, PRs, deploy scripts, running systems) BEFORE drafting. Never draft a reply based solely on transcripts or conversation memory. The user's credibility depends on accuracy.
- **Use the mandatory draft format below** for every draft message. No exceptions.
- **Do NOT remove content** from the action plan — it is append-only (mark done, don't delete).

#### Draft Message Format (MANDATORY)

Every draft must use this exact structure. The user's workflow is: glance at where to send, copy-paste the message, then verify grounding. Format accordingly.

```markdown
### Draft N: [short description]
**Send to:** #channel-name — reply to @Author Name's message at Wed Apr 2, 10:59 AM EDT (TS: 1775141956.643419)
— OR for new messages —
**Send to:** #channel-name — new message (not a thread reply)

` ` `
[Message text — ready to copy and paste exactly as-is]
` ` `

**Grounding:**
- [Verified fact 1 — what source confirmed it]
- [Verified fact 2 — what source confirmed it]
- [Any staleness risk — e.g., "No new replies in thread since 11:23 AM"]
```

**Field rules:**

1. **Send to** comes first. Must include:
   - Channel name (e.g., `#le-csa-feedback`)
   - Thread reply vs. new message
   - If thread reply: the **author's name** and **human-readable date+time** of the parent message (e.g., "Thu Apr 2, 10:59 AM EDT")
   - Unix TS in parentheses after the human time — the user doesn't need it but the agent uses it for re-reading threads

2. **Message text** comes second, in a fenced code block. This is what the user copies and pastes. Nothing else should be between "Send to" and the code block.

3. **Grounding** comes third. Bullet list of facts verified against primary sources (code, git, deploy logs, Slack threads). Must include:
   - What was verified and where (file path, commit hash, GH Actions run ID, thread TS)
   - Staleness check — whether anything has happened since the draft was written that could make it wrong
   - Any facts the agent could NOT verify (flag explicitly so the user knows)

**When marking drafts as SENT:**
```markdown
### ~~Draft N: [description]~~ ✅ SENT by Rajiv at Thu Apr 2, 6:16 PM EDT in #channel-name
```
Include the human-readable time the message was found in Slack.

---

## Transcript File Format

Each transcript type has its own file under `{workspace}/`. The internal format is the same across all three — only the header differs.

### Channels file (`{workspace}/channels/YYYY-MM-DD.md`)

```markdown
# Slack Channels — [Day], [Month] [Date], [Year]
# Workspace: [workspace]

Last synced: ~HH:MM TZ

---

## #channel-name (CHANNEL_ID)

### [Author Name] — HH:MM TZ (TS: [unix_timestamp])
[Message content]
**Thread ([N] replies):**
- [Reply Author] HH:MM (TS: [unix_timestamp]): "[reply text]"
- [Reply Author] HH:MM (TS: [unix_timestamp]): "[reply text]"
**Reactions:** [emoji_name] ([count])

---

## Mid-day sync (~HH:MM TZ)

### #channel-name

#### [Context heading] (TS: [unix_timestamp]) — [N] replies
- [New reply details]

---
```

### DMs file (`{workspace}/dms/YYYY-MM-DD.md`)

```markdown
# Slack DMs — [Day], [Month] [Date], [Year]
# Workspace: [workspace]

Last synced: ~HH:MM TZ

---

## DM with [Person Name] (DM_CHANNEL_ID)

### [Author Name] — HH:MM TZ (TS: [unix_timestamp])
[Message content]

---
```

### Group DMs file (`{workspace}/group-dms/YYYY-MM-DD.md`)

```markdown
# Slack Group DMs — [Day], [Month] [Date], [Year]
# Workspace: [workspace]

Last synced: ~HH:MM TZ

---

## Group DM: [Group Name or Members] (GROUP_DM_ID)

### [Author Name] — HH:MM TZ (TS: [unix_timestamp])
[Message content]

---
```

Key rules:
- **Always record the TS (Unix timestamp)** for every significant message. TSs are the key to re-reading threads later.
- **Note reply counts** so the next sync can detect new replies.
- **Separate sync sessions** with a horizontal rule and a timestamp header.
- **Each file type only contains its own message type.** Channels file has no DMs; DMs file has no channel messages.

---

## Date Verification

Before writing or naming any dated file, cross-check the date against at least two independent signals:

1. Slack Unix timestamps (convert with `date -r TS`)
2. Day-of-week clues in message content
3. User statements about the current day

The `currentDate` system value is a snapshot from session start. If a session crosses midnight, all subsequent dates will be wrong.

---

## Following Continuing Conversations

When a channel message references or continues an earlier discussion (broadcast replies, "also sent to channel," or topic continuations):

1. Grep local transcripts for the topic/keywords to find the parent message and its TS.
2. Read the parent thread via MCP using that TS — this surfaces all new replies.
3. Update the local transcript with any new thread replies.

**Do NOT search Slack MCP repeatedly.** Local transcripts are the source of truth for historical context. The point of syncing is to avoid depending on the MCP API for lookups.

---

## Error Handling

- **Slack MCP auth failure:** Stop immediately. Instruct user to run `claude mcp auth slack` and restart.
- **Channel not found:** The channel ID may have changed or the bot may have been removed. Warn and skip.
- **Rate limiting:** If Slack returns rate limit errors, wait and retry. Do not skip channels.
- **Empty channel:** Record "No new messages" in the transcript. Do not silently skip.

---

## When This Skill Runs

This skill is invoked:
- **By the user** typing `/synthesis-slack-sync` or "sync from Slack" or similar
- **By `synthesis-daily-rituals`** during Day-Start (Step 2: Sync), Mid-Day Sync, and Day-End (Step 1: Transcript Sync)
- **Before drafting any Slack reply** — the daily-rituals skill requires re-reading the actual thread before drafting, to avoid stale-information replies

---

## Why Each Step Matters

These steps were developed through real incidents, not theory:

- **Step 2 (thread re-reading):** On 2026-03-24, a mid-day sync skipped thread re-reads. The action plan showed a draft as "unsent" when the user had already sent it hours earlier. The agent proposed sending it again, which would have been a duplicate message.
- **Step 4 (save to local):** Transcripts are the persistence layer. Without them, every sync starts from scratch, re-reading entire channels. With them, syncs are incremental and fast.
- **Step 5 (action plan update):** The action plan is the user's dashboard. If it shows stale information (unsent drafts that were sent, unresolved items that were resolved), the user makes wrong decisions.
