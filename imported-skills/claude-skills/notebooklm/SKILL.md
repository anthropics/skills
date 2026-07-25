---
name: notebooklm
description: "Browser automation skill for controlling Google's NotebookLM. Use when the user wants anything done in NotebookLM (e.g., 'open NotebookLM', 'check my [name] notebook', 'ask my notebook about X', 'add [source] to NotebookLM', 'generate a Video Overview from my notebook', 'use NotebookLM Studio'). Handles reading and querying notebooks, adding sources (URLs, text, files, YouTube links, synthesized content), generating Studio outputs (Audio/Video Overviews, Mind Maps, Reports incl. Briefing Doc/Study Guide/FAQ, Flashcards, Quiz, slide decks, infographics — discover the exact set from the live Studio panel; the UI evolves fast), and creating new notebooks. Requires browser automation environment — fails gracefully when unavailable."
license: MIT
metadata:
  source_spec: "megaprompts/03-notebooklm-megaprompt.md"
  build_pattern: "Path B (direct conversion)"
  shape: "browser-automation (distinct from research-pack convention)"
  version: 1.0.0
---

# NotebookLM — Browser Automation

> **Requires:** A browser automation environment (Claude Code CLI with computer-use, Claude Chrome Extension, or equivalent). **Skill will gracefully fail in non-automation contexts with a clear "not supported" message.**

> **Critical:** This skill is the only browser-automation skill in the v2 collection. It does NOT follow the research-pack Agent Integrity Rules convention. Different constraints apply (UI dynamics, async generation, login walls).

## Step 0: Browser Context Setup (Mandatory)

Before any other action, verify browser automation is available:

1. Check whether browser-control tools are loaded in the harness (screenshot, click, find-element, navigate)
2. If unavailable → **halt with clear message:** "This skill requires browser automation. Currently in {context}. Cannot proceed. Use Claude Code CLI with computer-use, Claude Chrome Extension, or equivalent."
3. If available → take initial screenshot, navigate to https://notebooklm.google.com
4. **Detect login wall via screenshot.** If login screen detected: halt with "Please log in to NotebookLM in the browser, then re-invoke this skill." **Never attempt to handle login automatically.**

## Phase 0: Grill-Me Intake (Action-Routing)

Up to 4 forcing questions, one at a time, dependency-ordered. Most invocations stop at Q3.

### Q1 (root) — Action

> **What do you want me to do? Pick one:**
>
> 1. **Read / extract** — ask a question of an existing notebook
> 2. **Add a source** — push content (URL, text, file, Google Doc, or synthesized content) into a notebook
> 3. **Generate a Studio output** — Audio/Video Overview, Mind Map, Report (Briefing Doc, Study Guide, FAQ, Timeline), Flashcards, Quiz, Infographic, or Slides — the exact set comes from the live Studio panel
> 4. **Create a new notebook** — initialize with title + initial sources
>
> *Why I'm asking:* Each action takes a different path through the UI and requires different parameters. Naming the action upfront prevents wasted screenshots and lets me ask only the follow-up questions that apply.

**Forcing choice.** If the user says "open NotebookLM" without specifying an action, **refuse to start** and re-ask Q1.

### Q2 (depends on Q1) — Notebook identity

> **Which notebook?** *(asked for actions 1, 2, 3 — not for "create new")*
>
> *Why I'm asking:* If you give me a name, I'll search the homepage; if you give me a URL, I'll navigate directly. Names that are ambiguous will get a disambiguation prompt with screenshots.

For action 4 (create new): replace with "What's the title for the new notebook?"

### Q3 (depends on Q1) — Action-specific parameter

**Action 1 (read/extract):**
> "What's the question to ask the notebook? Use natural phrasing — the notebook's chat handles it best."

**Action 2 (add source):**
> "What source type? Pick one:
> 1. URL / website / YouTube link
> 2. Copied text (paste here or point at content)
> 3. File upload (provide absolute path)
> 4. Google Doc (link)
> 5. Synthesized content (I'll pre-process and add as 'Copied text')
>
> *Why I'm asking:* Each source type goes through a different sub-flow in the Add Source dialog. Picking upfront saves a step."

**Action 3 (Studio output):**
> "Which Studio output? As of 2026-06 the Studio panel offers Audio Overview, Video Overview, Mind Map, Reports (Briefing Doc / Study Guide / FAQ / Timeline / custom), Flashcards, Quiz, Infographic, and Slides — I'll screenshot the live panel and confirm what your account actually shows before clicking. And: any custom-prompt direction? **Default prompts produce mediocre output — I always open the customization menu and write a detailed prompt.** Tell me the angle or audience.
>
> *Why I'm asking:* The output type sets the UI button to find. The custom prompt is mandatory for quality."

**Action 4 (create new):**
> "Initial sources? Provide URLs, file paths, or 'I'll add later'."

### Q4 (depends on Q1 = action 3) — Studio custom prompt detail

> **Tell me the angle, audience, and length for the Studio output. Examples:**
>
> - **Audio Overview:** "Two-host conversation for a non-technical executive, 8–10 min, focus on business implications not technical depth"
> - **Infographic:** "Decision-tree style, action-oriented, 6 panels max, monochrome navy"
> - **Study Guide:** "Undergrad-level, definitions + 3 practice questions per concept"
>
> *Why I'm asking:* This becomes the custom prompt. **Default Studio prompts produce mediocre output — specific direction produces sharp output.**

**Asked only for Studio output generation (Q1=3). Skip otherwise.**

**Stop condition:** After Q4 (or earlier with dependency skips), commit and start the action sequence.

See [`references/studio_output_custom_prompts.md`](references/studio_output_custom_prompts.md) for the canon.

## Notebook Discovery

For actions 1-3 (require existing notebook):

1. Navigate to homepage → screenshot
2. If user provided **URL** → navigate directly
3. If user provided **name**:
   - Use semantic find() to locate notebook card by visible title text
   - If multiple matches → screenshot homepage, list options, ask user to specify
   - If no match → ask user to provide URL or confirm spelling

For action 4 (create new):
1. Locate "New notebook" button on homepage
2. Click → set title from Q2
3. Add initial sources per Q3

## Action 1: Read / Extract

1. Open the notebook (notebook discovery above)
2. Locate chat input (semantic find or screenshot coordinates)
3. Type the question (use the user's natural phrasing from Q3)
4. Submit (Enter or send button)
5. **Wait 3–5 seconds**
6. Screenshot the response area
7. Extract and present in **clean format** (not raw chat dump)

## Action 2: Add Sources

Sub-flows per source type:

| Type | UI flow |
|---|---|
| URL / Website / YouTube | Add Source → Link → paste URL |
| Copied Text | Add Source → Copied text → paste content |
| File Upload | Use file-upload tool with absolute path + input ref (never click native file picker) |
| Google Doc | Add Source → Google Docs → Drive picker |
| Synthesized content | Pre-process content elsewhere, then add as Copied text |

**After every add:** wait for ingestion spinner, screenshot to confirm success.

**Synthesized content pattern (powerful):** instead of asking NotebookLM to ingest a raw URL with potentially noisy content, pre-process the content (extract main article, strip nav/ads/comments), then add as "Copied text". Produces dramatically better summarization.

## Action 3: Studio Outputs

**Discover, don't assume.** NotebookLM's Studio inventory changes between rollouts and account tiers. As of the last verification (2026-06) the panel offers: **Audio Overview, Video Overview, Mind Map, Reports** (Briefing Doc, Study Guide, FAQ, Timeline, custom report formats), **Flashcards, Quiz, Infographic, Slides**. Treat this list as a hint, not ground truth — the screenshot of the live Studio panel is the authority. NotebookLM's UI evolves quickly; verify against the live product and update this section when it drifts (Studio inventory last verified 2026-06).

**Mandatory workflow:**

1. Locate Studio panel (right side; may need toggle) and **screenshot it — the tiles you see are the real output types for this account**
2. Find the specific output button for the requested type (if it isn't visible, check "Discover more"/overflow before declaring it unavailable)
3. **Open customization menu** (chevron/arrow next to button) — **NOT the main button**
4. **Write detailed custom prompt** (from Q4)
5. Confirm and submit
6. **Do NOT wait for completion** — confirm generation started, notify user, return

### Custom prompt examples (4 output types)

**Audio Overview:**
> "Two-host conversation between a researcher and an experienced practitioner. Audience: non-technical executive making a budget decision. Length: 8-10 minutes. Focus on business implications, not technical depth. Include one concrete example per major point. Acknowledge counter-arguments briefly."

**Infographic:**
> "Decision-tree style. Action-oriented (each panel ends with a decision or action). 6 panels max. Monochrome navy + amber highlight. Each panel has: title (4-6 words), 1-2 sentence body, decision/action line. No filler panels."

**Study Guide:**
> "Undergraduate-level (define every technical term). Structure: 6 concepts × 4 elements each (definition / why it matters / one worked example / 3 practice questions). Practice questions Bloom-higher-order (apply/analyze), not recall."

**Slides (slide deck):**
> "12 slides max. 1-2 sentences per slide body. Presenter notes per slide with: one concrete example + one likely audience objection + how to address it. No bullet points in slide bodies — prose only. End with one-slide call-to-action."

See [`references/studio_output_custom_prompts.md`](references/studio_output_custom_prompts.md) for more.

## Action 4: Create New Notebook

1. Navigate to homepage
2. Click "New notebook"
3. Set title from Q2
4. Add initial sources from Q3 (use Action 2 sub-flows per source type)
5. **Wait for auto-summary generation** (this one IS synchronous — usually completes in <30 sec)
6. Screenshot final state

## Critical Async Behavior

> **Async output rule:** For Studio generations (especially **Audio Overview** — 5-10 min), DO NOT wait for completion. The user's session will time out.
>
> Workflow: Click Generate → confirm generation has started via screenshot → tell the user "Generation in progress — NotebookLM will notify you when ready" → **end the task.**

This is the **fire-and-notify** pattern. Different from add-source and auto-summary (which are fast enough to wait).

Use `scripts/async_action_classifier.py` to determine wait-or-notify per action:

| Action | Wait? |
|---|---|
| Add Source (URL/text/file) | Yes — wait for ingestion spinner (~5-30s) |
| Read/Extract (chat) | Yes — wait 3-5s for response |
| Studio: Audio Overview | **No** — fire and notify (5-10 min) |
| Studio: Video Overview | **No** — fire and notify (5-15 min) |
| Studio: Infographic / Slides / Mind Map | **No** — fire and notify (2-5 min) |
| Studio: Study Guide / Briefing Doc / FAQ / Flashcards / Quiz | Yes — wait ~30-60s |
| Create New Notebook | Yes — wait for auto-summary (<30s) |

```bash
# Verdict + paste-ready notify message for any action
python3 scripts/async_action_classifier.py --action "video overview"
# -> Verdict: FIRE_AND_NOTIFY, estimated 5-15 minutes, with the exact
#    "NOT waiting in this session" message to relay to the user
```

See [`references/async_action_discipline.md`](references/async_action_discipline.md) for the canon.

## Screenshot-First Discipline

NotebookLM is a **dynamic SPA** where UI varies by:
- Account tier (free vs Plus vs Enterprise)
- Feature rollout (some Studio types not yet available to all users)
- Recent UI changes (Google iterates the product frequently)

**Every UI action must be preceded by a screenshot.** Reasons:

1. Verify the UI matches expectations before acting
2. Catch login walls early
3. Detect unexpected layout changes
4. Audit trail for debugging

Use `screenshot()` (or equivalent in your browser-automation tool) before every meaningful UI interaction.

See [`references/browser_automation_canon.md`](references/browser_automation_canon.md) for the discipline.

## find()-Before-Click

Use **semantic element finders** before pixel coordinates wherever possible:

- ✅ `find(text="Audio Overview")` → returns element regardless of position
- ❌ `click(x=420, y=380)` → breaks when UI rearranges

Semantic finders survive minor UI changes. Pixel coordinates do not.

Only fall back to coordinates when:
- Semantic find() returns nothing
- Element has no stable text/aria-label/data-attribute
- Visual position is the only reliable signal

## Saving Outputs to Workspace

For Read/Extract actions producing useful information:

1. Extract chat response cleanly (strip UI chrome)
2. Format readably (paragraphs, lists, code blocks as appropriate)
3. If user requested → save to file (`${WORKSPACE}/notebooklm/<notebook-slug>-<action>-<date>.md`)
4. Otherwise → return in chat as final summary

For Studio outputs:
1. NotebookLM hosts the output (Audio Overview is in-app, Infographic downloadable, etc.)
2. Report the location (URL or in-app navigation path) to user
3. Don't try to download/save Studio outputs to local workspace — that's NotebookLM's job

## Reporting Back Format

After completing any action:

1. Take final screenshot if visually relevant
2. Give **clean summary** (not raw chat dump):
   - Notebook used (name)
   - Action taken (specific)
   - Result (1-2 sentences)
   - For generated outputs: what was created + where it is + when ready
3. For fire-and-notify actions: explicit "NotebookLM will notify you when ready"

## Error Handling

| Failure | Behavior |
|---|---|
| Browser automation unavailable | Fail fast with "this skill requires browser automation" message (Step 0 halt) |
| Login wall detected | Stop. Tell user to log in. Don't attempt auto-login. |
| Multiple notebooks match name | Screenshot homepage, list options, ask user to specify |
| Source ingestion spinner stuck > 60s | Note timeout, ask user if they want to retry |
| Studio button not found in panel | Scroll down or look for "Discover more"; if still missing, note feature may not be enabled for this account |
| Chat response doesn't appear in 10s | Screenshot, check for error state, retry once |
| Page layout changed unexpectedly | Screenshot, describe what's visible, ask user for guidance |

## Tooling

| Script | Role |
|---|---|
| `scripts/action_router.py` | Q1-Q4 answers → action plan + UI flow + required parameters |
| `scripts/custom_prompt_template_generator.py` | Studio output type + audience + length → starter custom prompt |
| `scripts/async_action_classifier.py` | Action name → wait-or-notify pattern (fire-and-notify for slow generations) |

## References

- [`references/browser_automation_canon.md`](references/browser_automation_canon.md) — screenshot-first + find-before-click + tool-agnostic patterns (7+ sources)
- [`references/studio_output_custom_prompts.md`](references/studio_output_custom_prompts.md) — why defaults are mediocre + per-output-type templates (7+ sources)
- [`references/async_action_discipline.md`](references/async_action_discipline.md) — fire-and-notify pattern for slow UI ops (7+ sources)

## Anti-Patterns To Reject

- Tool-specific tool names without abstraction (e.g., hardcoding "Claude Chrome Extension")
- Synchronous waiting on Studio generations (especially Audio Overview)
- Skipping screenshots between actions
- Using pixel coordinates when semantic find() is available
- Attempting to handle login flows automatically
- Generating Studio outputs without opening customization menu
- Using default Studio prompts (always write custom)

---

**Version:** 1.0.0
**Source spec:** [`megaprompts/03-notebooklm-megaprompt.md`](../../../../megaprompts/03-notebooklm-megaprompt.md)
**Build pattern:** Path B (direct conversion). Browser-automation shape — distinct from research-pack convention.
