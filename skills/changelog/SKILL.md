---
name: changelog
description: Generate a weekly changelog card for Twitter/X. Reads git log, distills the work into 6 punchy items, fills an HTML template, and opens it in the browser. Use when writing changelogs, weekly updates, or social media posts about shipped work.
license: Apache-2.0
---


Generate the weekly changelog Twitter card. Run every Friday (or whenever you ship).

## Steps

### 1. Get this week's commits
```bash
git log --oneline --since="7 days ago"
```

Get the stats:
```bash
# Commit count
git log --oneline --since="7 days ago" | wc -l

# Files + lines changed
git log --since="7 days ago" --pretty=tformat: --numstat | awk '{files++; add+=$1; del+=$2} END {print files " files · " add+del " lines"}'
```

### 2. Understand what actually shipped
Read each commit message. For any that are unclear, look at the diff:
```bash
git show [commit-hash] --stat
```
Group commits into themes. Ignore pure refactors, dependency bumps, and test fixes — users don't care. Focus on what changed for them.

### 3. Distill into exactly 6 items
Each item needs:
- **An emoji** that fits the work (✨ new feature, 🐛 fix, ⚡ performance, 🎨 design, 🔒 security, etc.)
- **A short title** — 3-5 words, lowercase, punchy
- **2-3 lines of body** — explain the user benefit, not the technical detail. Write like a human, not a release note. "credits update in real time" not "implemented shared zustand store for credit synchronisation."

If fewer than 6 meaningful things shipped, combine small related items or include one "under the hood" item about stability/performance.

### 4. Find or create the changelog template
Look for a `changelogs/` directory in the repo. If there's a `template.html`, use it.

If no template exists, create `changelogs/template.html` with this structure:
```html
<!DOCTYPE html>
<html>
<head>
  <meta charset="UTF-8">
  <style>
    * { margin: 0; padding: 0; box-sizing: border-box; }
    body {
      width: 1200px; height: 628px; overflow: hidden;
      background: #09090b; font-family: 'JetBrains Mono', ui-monospace, monospace;
      display: flex; flex-direction: column; padding: 48px;
    }
    .header { color: #71717a; font-size: 13px; margin-bottom: 32px; letter-spacing: 0.05em; }
    .header span { color: #fafafa; }
    .grid { display: grid; grid-template-columns: 1fr 1fr; gap: 20px; flex: 1; }
    .item { display: flex; gap: 12px; }
    .emoji { font-size: 18px; flex-shrink: 0; margin-top: 1px; }
    .content h3 { color: #fafafa; font-size: 13px; font-weight: 700; margin-bottom: 4px; }
    .content p { color: #71717a; font-size: 11px; line-height: 1.6; }
    .content p strong { color: #a1a1aa; }
    .footer { color: #3f3f46; font-size: 11px; margin-top: 24px; letter-spacing: 0.05em; }
  </style>
</head>
<body>
  <div class="header">what shipped this week · <span>MONTH DAY</span></div>
  <div class="grid">
    <div class="item"><div class="emoji">EMOJI</div><div class="content"><h3>TITLE</h3><p>BODY LINE 1<br>BODY LINE 2<br><strong>BODY LINE 3</strong></p></div></div>
    <!-- repeat 5 more times -->
  </div>
  <div class="footer">N commits · N files · N lines · all live</div>
</body>
</html>
```

### 5. Create this week's file
Create `changelogs/YYYY-MM-DD.html` (use today's date).

Fill in:
- Header date (e.g. "what shipped this week · march 1")
- All 6 items
- Footer stats from step 1

### 6. Open in browser
```bash
open changelogs/YYYY-MM-DD.html
```

Tell the user: "ready — screenshot the browser window (⌘+Shift+4 on Mac) and post it."

## Voice
Lowercase. Direct. No buzzwords. User benefit first, technical detail never. If you can't explain the value to a non-engineer in one line, rewrite it.

## Design rule
If using an existing template — never touch the CSS. Content only. The design is locked.
