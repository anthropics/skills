# instant-deploy skill

## Trigger
Activate this skill when the user asks to:
- "create a website / page / landing page"
- "deploy / publish / go live"
- "make a page for X"
- "build a site from this content"
- Any variation of turning content into a live URL

---

## Workflow

### Step 1 — Gather content
If content is already present in conversation context (copy, spec, research, pitch deck, deal page, etc.), use it directly.
Otherwise ask:
> "מה תוכן הדף? שלח טקסט, נקודות, או כל חומר גלם."
> ("What's the page content? Send text, bullet points, or raw material.")

---

### Step 2 — Choose template
| Content type | Template |
|---|---|
| Research / article / report / study / deep-dive | `dark-teal` |
| Product / service / SaaS / landing / pitch | `landing` |
| Portfolio / bio / minimal blog / statement | `minimal` |

When in doubt, default to `dark-teal`.

---

### Step 3 — Generate the HTML

Rules:
1. **Language**: Hebrew RTL by default (`dir="rtl"` on `<html>`, `direction: rtl` in CSS). Switch to LTR only if content is explicitly English.
2. **Fonts**: Always load from Google Fonts:
   - Hebrew: `Heebo` (body) + `Frank Ruhl Libre` (headings/display)
   - English: `DM Mono` or `Syne` (headings) + `Lora` (body)
3. **Theme**: Dark background, accent per template palette (see below).
4. **Grain overlay**: Always include CSS noise texture on `body::before` using `filter: url(#noise)` or SVG base64 data URI.
5. **Animations**: Intersection Observer fade-up on all `.animate` elements. CSS transition + `opacity/translateY`.
6. **Responsive**: Mobile-first, max-width 1100px container, fluid type with `clamp()`.
7. **Self-contained**: Single HTML file, zero external JS dependencies beyond Google Fonts.

Inject the user's content into the chosen template structure. Map content semantically:
- Long body text → section paragraphs
- Short bullets → card grid or stat bar
- Numbers/metrics → hero stats
- Steps/process → timeline
- Pros/cons or comparisons → comparison table
- Call to action phrase → CTA section

Save final file to:
```
/home/claude/deploy-output/index.html
```

---

### Step 4 — Deploy

Run:
```bash
bash /path/to/instant-deploy/scripts/deploy.sh "<page-title-in-english>"
```

The script will:
- Slugify the title → Cloudflare Pages project name
- Run `wrangler pages deploy /home/claude/deploy-output --project-name <slug>`
- Print the live URL

---

### Step 5 — Return URL

Reply with:
```
✅ הדף עלה לאוויר:
https://<slug>.pages.dev
```

---

## Template Palettes

### dark-teal
```
--bg:       #0a0f0f
--surface:  #111a1a
--border:   #1e3030
--accent:   #00e5c8
--accent2:  #007a6a
--text:     #e8f4f2
--muted:    #6b9e98
```
Components: numbered sections with oversized section numbers, animated fade-up, hero with stat bar, card grid (3-col), comparison table, callout boxes with left border accent, timeline with connector line, CTA section with radial glow behind button.

### landing
```
--bg:       #080810
--surface:  #0f0f1e
--border:   #1e1e3a
--accent:   #7c6af7
--accent2:  #4a3fc7
--text:     #f0eeff
--muted:    #7070a0
```
Components: split hero (text left, visual right), feature list with icons, pricing tiers, testimonial strip, sticky nav, footer with links.

### minimal
```
--bg:       #f7f5f0
--surface:  #ffffff
--border:   #e8e4dc
--accent:   #1a1a1a
--accent2:  #555555
--text:     #1a1a1a
--muted:    #888888
```
Light theme. Components: large typographic hero, single-column article layout, pullquotes, footnotes, minimal nav.

---

## File locations (after plugin install)
```
~/.claude/plugins/instant-deploy/
  skills/instant-deploy/SKILL.md    ← this file
  templates/dark-teal.html
  templates/landing.html
  templates/minimal.html
  scripts/deploy.sh
  .claude-plugin/marketplace.json
```

Output always goes to:
```
/home/claude/deploy-output/index.html
```
