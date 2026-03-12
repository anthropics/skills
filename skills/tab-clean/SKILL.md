---
name: tab-clean
description: AI-powered Chrome tab cleanup — classifies tabs as KEEP/SAVE/CLOSE, extracts interest signals from searches, and discusses context before closing.
license: MIT
---

# /tab-clean - Chrome Tab Cleanup

Read all Chrome tabs, classify them, discuss context with the user, then close/save as confirmed.

## Procedure

### Step 1: Collect tabs

**Pre-check: Is Chrome running?**
```
osascript -e 'application "Google Chrome" is running'
```
If `false` → tell the user: "Chrome is not running. Please open Chrome first." and **stop**.

**Collect all tabs:**
```
osascript -e '
tell application "Google Chrome"
  set output to ""
  set winCount to count of windows
  repeat with w from 1 to winCount
    set tabCount to count of tabs of window w
    repeat with t from 1 to tabCount
      set tabTitle to title of tab t of window w
      set tabURL to URL of tab t of window w
      set output to output & "W" & w & "|T" & t & "|" & tabTitle & "|" & tabURL & linefeed
    end repeat
  end repeat
  return output
end tell'
```
Parse into `{window, index, title, url}` list.

If total tab count is 0 → tell the user: "No tabs found. Nothing to clean." and **stop**.

**Pinned tabs:** After collecting, ask the user: "How many of your leftmost tabs are pinned?" Mark those as auto-KEEP. If the user says "none", skip this.

### Step 2: Auto-classify

Classify each tab into 3 categories:

| Category | Action |
|----------|--------|
| **KEEP** | Do not close |
| **SAVE** | Save to `./tabs-{YYYY-MM-DD}.md` with context, then close |
| **CLOSE** | Close immediately |

#### Default KEEP domains (auto-KEEP, skip questions)
- `mail.google.com`
- `calendar.google.com`
- `discord.com`
- `slack.com`
- `linear.app`
- `notion.so`
- `linkedin.com/feed`, `linkedin.com/in/`
- `docs.google.com`

> **Customize:** Add your own KEEP domains below (e.g., `github.com/{username}`, `{company}.atlassian.net`)

#### CLOSE candidates (AI judgment)
- Already-consumed individual SNS posts (single tweet on x.com, single Instagram post)
- Completed transaction/order pages
- Chrome extension internal pages (`chrome-extension://`)
- Duplicate tabs
- `chrome://newtab/`

#### SAVE candidates (AI judgment)
- Unread technical articles, blog posts
- Research/comparison pages worth revisiting
- Tab groups with apparent intent (multiple tabs from the same domain suggesting a research thread)

#### Interest Signal extraction (Google searches)
Google search tabs (`google.com/search`) are CLOSE'd, but **extract the search query as an Interest Signal** first. Only extract searches related to: software engineering, AI/tech, business, startups, career, product. Skip mundane searches (weather, directions, etc.).

### Step 3: Context conversation

#### Large tab sets (30+ non-KEEP tabs)
If there are more than 30 non-KEEP tabs:
- Group by domain only (not topic) for efficiency
- Show summary first: "{N} non-KEEP tabs across {M} domains"
- Ask: "Want to review all groups, or only groups with 3+ tabs?"
- Single-tab groups without clear intent → auto-suggest CLOSE

#### Grouping
Group non-KEEP tabs by similar URL/domain/topic. **Ask per group, NOT per tab.**

For each group, ask the user:
```
## Group: {domain/topic} ({N} tabs)
- {tab1 title}
- {tab2 title}
...

Why did you have these open?
1. Still an active research/task → KEEP
2. Had an idea/intent → please describe the context (will be recorded in SAVE)
3. Already done → CLOSE
```

If the user provides context (option 2), capture it verbatim for the SAVE record.

### Step 4: Final confirmation

Show the classification reflecting the conversation:

```
## KEEP ({N}) — staying open
- {tab name}
...

## SAVE ({N}) → saving then closing
- [{title}]({URL}) — {one-line context description}
...

## CLOSE ({N}) — closing
- {tab name}
...

## Interest Signals (from searches)
- **{search query}** — {one-line interpretation of why this matters}
...

Any changes? If not, say "confirm".
```

Proceed to Step 5 only after user confirms.

### Step 5: Execute

1. **Create/append `./tabs-{YYYY-MM-DD}.md`**:
   - **Top section**: `## Interest Signals (from Google searches)` — accumulated search signals with one-line context
   - **Below**: `## Saved Tabs` — grouped SAVE tabs with `- [{title}]({URL}) — {context}`
   - If file already exists for today, append new entries (don't overwrite)
   - Save path can be customized (e.g., `inbox/tabs-{date}.md` for Obsidian users)

2. **Close tabs** (both CLOSE and SAVE targets):
   - Re-collect all tab URLs right before closing (tabs may have shifted during conversation)
   - Match tabs to close by URL substring
   - **Iterate ALL windows, and within each window close tabs in reverse index order** (handles multi-window)
   - Pass all URL patterns in a single `osascript` call:
     ```
     tell application "Google Chrome"
       set closedCount to 0
       set winCount to count of windows
       repeat with w from 1 to winCount
         set tabCount to count of tabs of window w
         repeat with t from tabCount to 1 by -1
           set tabURL to URL of tab t of window w
           -- check against each URL pattern
           if tabURL contains "{pattern1}" or tabURL contains "{pattern2}" ... then
             close tab t of window w
             set closedCount to closedCount + 1
           end if
         end repeat
       end repeat
       return "Closed " & closedCount & " tabs"
     end tell
     ```
   - Build the `if` condition dynamically from the list of CLOSE+SAVE URLs
   - This approach is window-agnostic: works regardless of how many windows are open or which window contains the tabs

### Step 6: Summary

```
Tab cleanup complete:
- KEEP: {N} tabs kept
- SAVE: {N} tabs → saved to tabs-{date}.md, then closed
- CLOSE: {N} tabs closed
- Interest Signals: {N} search queries captured
```
