# Async Action Discipline — Fire-and-Notify for Slow UI Operations

This reference answers exactly one decision: **for each NotebookLM action, does the skill wait synchronously OR fire and notify the user?**

## The Core Trade-Off

Browser-automation sessions have practical time limits:

- **Claude Code CLI sessions:** typically time out after ~10 minutes of inactivity
- **Chrome Extension sessions:** depend on the user keeping the tab open
- **API contexts:** strict timeout (60s-5min depending on tier)

NotebookLM's Studio operations vary in completion time:

- **Audio Overview:** 5-10 minutes (model generation + audio synthesis)
- **Infographic / Slides / Mind Map:** 2-5 minutes (complex visual generation)
- **Study Guide / Briefing Doc / FAQ:** 30-60 seconds (text generation)
- **Add Source ingestion:** 5-30 seconds (parsing + indexing)
- **Auto-summary on new notebook:** 10-30 seconds

The mis-match between session timeout and operation time means **synchronous waiting on slow ops is a failure mode**. The skill must fire-and-notify for slow operations instead.

## The Fire-and-Notify Pattern

When triggering a slow operation:

1. Locate the trigger button (via find())
2. Click it
3. **Verify generation started** via screenshot (look for spinner / "Generating" indicator)
4. **Tell the user**: "Generation in progress — NotebookLM will notify you when ready. NotebookLM sends in-app and email notifications when complete."
5. **End the task** — return control to the user

Key: **don't loop waiting for completion**. The browser-automation session will time out before NotebookLM finishes.

The user already knows how NotebookLM works — they'll see the notification when the Audio Overview is ready. The skill's job is to confirm the generation **started**, not to babysit it to completion.

## Per-Action Timing Catalog

| Action | Type | Timing | Wait or Notify? |
|---|---|---|---|
| Chat send (Read/Extract) | Q&A | 3-10s | **Wait** (short) |
| Add Source: URL | Ingestion | 5-15s | **Wait** |
| Add Source: Text | Ingestion | 5-15s | **Wait** |
| Add Source: File upload | Ingestion | 10-30s | **Wait** (with 60s timeout) |
| Add Source: Google Doc | Ingestion | 10-30s | **Wait** (with 60s timeout) |
| Create New Notebook | Init + summary | 15-30s | **Wait** |
| Studio: Study Guide | Generation | 30-60s | **Wait** (with 90s timeout) |
| Studio: Briefing Doc | Generation | 30-60s | **Wait** (with 90s timeout) |
| Studio: FAQ | Generation | 30-60s | **Wait** (with 90s timeout) |
| Studio: Flashcards / Quiz | Generation | 30-60s | **Wait** |
| Studio: Video Overview | Generation | 5-15 min | **Fire-and-notify** |
| Studio: Timeline | Generation | 30-60s | **Wait** (with 90s timeout) |
| **Studio: Audio Overview** | Audio gen | **5-10 min** | **NOTIFY** (fire-and-notify) |
| **Studio: Infographic** | Visual gen | **2-5 min** | **NOTIFY** |
| **Studio: Slides** | Visual gen | **2-5 min** | **NOTIFY** |
| **Studio: Mind Map** | Visual gen | **2-5 min** | **NOTIFY** |

The dividing line: **>2 minutes → fire-and-notify**. Anything shorter, wait synchronously with appropriate timeout.

## Wait-Discipline Details

For "wait" actions, the discipline:

1. After clicking the trigger, **start a wait loop** with timeout
2. Poll for completion signal:
   - Spinner disappearing
   - "Done" / "Ready" indicator
   - Result content appearing
3. Take screenshot at intervals (every 10-15s) for audit
4. If timeout exceeded → screenshot, note timeout, ask user how to proceed

Example for chat (Read/Extract):

```
1. Submit question
2. Take screenshot at T+3s
3. If response present → extract, return
4. If still generating → take screenshot at T+8s
5. If response present → extract, return
6. If still not present → take screenshot at T+15s, note delay
7. If T+30s and still no response → note error, retry once
8. If second attempt fails → report failure with screenshot
```

## Notify-Discipline Details

For "notify" (fire-and-notify) actions:

1. Click Generate (in the customization menu, after custom prompt is set)
2. Take screenshot **within 5s** to verify generation started
3. Confirm via visible signal:
   - Spinner appearing
   - Status text changing to "Generating..."
   - Generate button disabled or replaced with "Cancel"
4. **Tell the user**:
   > "Generation triggered for {output_type}. NotebookLM takes ~{N} minutes for this. NOT waiting in this session — NotebookLM will notify you in-app and via email when ready. Returning control to you."
5. **End the task**. Don't loop.

## What Goes Wrong With Synchronous Waiting

### Failure 1: Session timeout

Skill clicks "Generate Audio Overview" at T+0. Browser-automation session times out at T+10min. Skill never confirms generation completed. User gets confused error message.

### Failure 2: Wasted compute

Skill loops `screenshot()` every 5s waiting for completion. 10 minutes × 12 screenshots/min = 120 wasted screenshots. Compute cost adds up.

### Failure 3: Hides errors

While waiting, if NotebookLM shows a transient error and recovers, the skill's wait loop might not catch it. Better: confirm started, hand off to NotebookLM's own error handling.

### Failure 4: Blocks user

User wanted to do something else while Audio Overview generated. Synchronous wait blocks the session.

## What Goes Wrong With Premature Notify

The opposite failure: applying fire-and-notify to a fast action.

### Anti-example: Read/Extract chat send

If the skill clicks send + immediately notifies "Response is being generated", the user has to come back later to retrieve it. But chat responses complete in 3-10s. Waiting is correct.

### Anti-example: Add Source URL

URL ingestion is 5-15s. The skill should wait for the ingestion spinner to clear, then confirm success. Premature notify means user doesn't know if the source was added successfully.

The 2-minute dividing line is empirically the right boundary. Below it, wait. Above it, notify.

## Tooling

`scripts/async_action_classifier.py` returns the wait-or-notify verdict per action:

```bash
python async_action_classifier.py --action audio_overview
# Returns: FIRE_AND_NOTIFY (estimated 5-10 min)

python async_action_classifier.py --action add_source_url
# Returns: WAIT (estimated 5-15s, timeout 60s)
```

Use this before triggering any Studio or Add-Source action so the skill applies the right pattern.

## Edge Cases

### Generation visibly fails immediately

If the Generate click results in an error toast within 5s → catch it, report, don't notify "in progress."

### Generation queued behind another generation

NotebookLM serializes Studio generations per notebook. If user requests Audio Overview while previous one is generating → either:
- Wait for previous to clear (only if previous is ~30s from completion based on visible progress)
- Notify: "Previous generation in progress; new one will queue"

### User cancels mid-generation

If user types "stop" while skill is in wait loop → stop polling, screenshot final state, report what was triggered.

## Anti-Patterns

### Synchronous wait on Audio Overview

The classic failure. 5-10 min wait exceeds session timeout.

### Fire-and-notify on chat send

Premature notify on fast action. User can't tell if it worked.

### No completion signal verification

Just clicking Generate and notifying without confirming generation started. If the click missed (semantic find on wrong element), the user thinks generation started when it didn't.

### Loop screenshot every 1s during wait

Wastes compute. 10-15s intervals are fine for waits.

### Ignore visible error toasts

If error appears, react. Don't proceed with "in progress" message if generation clearly didn't start.

## Operational Checklist (Per Action)

- [ ] Classify action via `async_action_classifier.py` (wait vs notify)
- [ ] If wait: set appropriate timeout (longer for file upload than chat)
- [ ] If notify: verify generation started via screenshot within 5s
- [ ] Tell user explicitly when fire-and-notify ("NotebookLM will notify you when ready")
- [ ] End task after notify — don't loop
- [ ] On wait timeout: screenshot + ask user how to proceed
- [ ] On visible error: report immediately

## Citations (7 sources)

1. **Anthropic API documentation — session timeout behavior.** Source for the 60s-5min API timeout ranges that motivate fire-and-notify for slow ops. https://docs.anthropic.com/

2. **Google NotebookLM Studio documentation + community findings (2024-2026).** Source for the per-output-type timing estimates (Audio Overview 5-10 min, Infographic 2-5 min, etc.). Empirical from user reports.

3. **Erlang / OTP "let it crash" philosophy (Joe Armstrong).** Source for the broader async pattern: don't wait for slow operations synchronously. Hand off + let the supervising system handle completion notifications.

4. **AWS Step Functions documentation.** Source for the fire-and-notify pattern in distributed systems. Step Functions explicitly distinguishes "Wait" tasks from "Callback" (fire-and-notify) tasks based on duration.

5. **Twelve-Factor App — Factor IX (Disposability).** Source for the "fast startup, graceful shutdown" discipline. Skills should be disposable — return control quickly rather than holding sessions open.

6. **Node.js event loop documentation.** Source for the async-event-loop discipline. Synchronous blocking on slow ops harms throughput; async handoff preserves it.

7. **Playwright + Selenium wait-strategy documentation.** Source for the polling-with-timeout pattern for "wait" actions. Both frameworks document the discipline of bounded waits with explicit timeouts.
