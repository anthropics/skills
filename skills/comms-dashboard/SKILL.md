---
name: comms-dashboard
description: "Build a personalized communications dashboard that pulls Slack messages, Outlook emails, and Google Docs activity, extracts action items by priority, and renders everything as an interactive HTML file. User chooses between a Standard (clean, professional) or Creative (bold Memphis style with daily tarot card) design. Auto-refreshes hourly during work hours. Use this skill whenever someone asks for a communications dashboard, wants to see what needs their attention across Slack/email/docs, asks about unread messages or action items, says things like 'what's on my plate', 'what do I need to respond to', 'show me my inbox', 'communications overview', 'activity dashboard', or wants a summary of their Slack, email, and Google Docs. Also triggers on: 'standard dashboard', 'clean dashboard', 'professional dashboard', 'creative dashboard', 'fun dashboard', 'colorful dashboard', 'Memphis dashboard', 'whimsical dashboard', 'tarot dashboard'."
---

# Communications Dashboard

Build a self-contained, interactive HTML dashboard that surfaces action items, Slack draft replies, emails needing attention, and recently active docs — all in one place. Comes in two styles: a clean professional layout and a bold, expressive Memphis design with a daily tarot card.

---

## Step 0 — Determine Style

If the user's message clearly signals a preference, go with it:
- "standard", "clean", "professional", "minimal", "simple" → **Track A: Standard**
- "creative", "fun", "colorful", "whimsical", "Memphis", "tarot", "bold" → **Track B: Creative**

Otherwise, ask before proceeding:

> "Which dashboard style would you like?"
> - **Standard** — Clean, professional layout. Easy to scan. No distractions.
> - **Creative** — Bold Memphis design with thick borders, saturated color, and a daily tarot card reading.

---

## Step 1 — Get the User's Name

Use `slack_read_user_profile` or `slack_search_users` to get the user's display name. Use it throughout the dashboard (e.g., "Jordan's Dashboard", "Alex's Action Items"). If unavailable, use "Your".

---

## Step 2 — Pull Data From All Sources

Run these searches simultaneously to gather the last 24 hours of activity.

**Slack** — Use the Slack search tools:
- Messages FROM the user: `from:<@USER_ID> on:YYYY-MM-DD`
- Messages TO the user: `to:<@USER_ID> on:YYYY-MM-DD`
- Sort by timestamp descending, limit 20 per query
- **IMPORTANT — Paginate to get the full count:** The Slack API returns max 20 results per page. For the "Slacks Sent" KPI, paginate through ALL pages of the FROM search using the `cursor` from `pagination_info`. Count ALL pages — users often send 100+ messages per day.

**Outlook Email** — Use the Outlook email search tool:
- Search for emails received in the last 24 hours using `afterDateTime`
- Limit 50 emails

**Google Docs** — Use the Google Drive search tool:
- Query: `modifiedTime > 'YYYY-MM-DDT00:00:00'`
- Order by modifiedTime desc, page_size 20

---

## Step 3 — Extract Action Items

This is the most important step. The user cares about what they need to **do**, not raw message volume.

**High Priority** (action needed today or tomorrow):
- Explicit requests with deadlines
- Urgent or time-sensitive DMs
- Unresponded questions in direct messages
- Meeting prep for imminent meetings

**Medium Priority** (this week):
- Project discussions awaiting input
- Review requests for documents or proposals
- Follow-ups from earlier conversations

**Low Priority / FYI**:
- Informational messages and confirmations
- Automated notifications
- Background context

**EXCLUDE entirely** (do NOT create action items):
- Meeting RSVPs — accepted, declined, or tentative with no other action required
- Automated calendar notifications unless they require a real action
- Marketing emails, newsletters, automated receipts

**Also identify:**
- **Slack messages needing a reply** — DMs and group messages where someone asked a question or made a request. For each, draft a friendly, professional reply and embed it in the dashboard. Also create an actual Slack draft using `slack_send_message_draft` (see Step 4).
- **Emails needing attention** — Unread important emails, action-required messages, review requests.

---

## Step 4 — Draft Replies & Slack Drafts

For every message needing a reply:

1. Use `slack_search_users` to look up the recipient's Slack user ID
2. Call `slack_send_message_draft` with the user ID as `channel_id` and the draft text as `message`
3. The tool returns a `channel_link` URL — **use this exact URL** for the "OPEN DRAFT" button in the dashboard HTML. This is the format that reliably opens in the Slack desktop app.
4. If `draft_already_exists` is returned, skip — a draft is already there

For Slack-sourced action items, add an "OPEN IN SLACK" link using the `channel_link` URL returned by `slack_search_users` or `slack_send_message_draft`. Do not hardcode workspace URLs.

**CRITICAL — Confidentiality:** Never include confidential information in the dashboard. If a message says "keep confidential", contains sensitive budget figures, or has information clearly not meant to be shared, redact it. Describe the topic generally (e.g., "Follow up with Jamie on Q3 budget implications") without exposing confidential details.

---

## Step 5A — Build the Standard Dashboard

Use this track when the user chose Standard or signaled a clean/professional preference.

### Design System

**CSS Custom Properties** (put at `:root` so it's easy to theme):

```css
:root {
  --primary: #2563EB;
  --primary-dark: #1D4ED8;
  --dark: #0F172A;
  --text: #1E293B;
  --text-muted: #64748B;
  --bg: #F8FAFC;
  --surface: #FFFFFF;
  --border: #E2E8F0;
  --high: #EF4444;
  --medium: #F59E0B;
  --low: #94A3B8;
  --green: #10B981;
  --radius: 8px;
  --shadow: 0 1px 3px rgba(0,0,0,0.08), 0 1px 2px rgba(0,0,0,0.04);
  --shadow-md: 0 4px 6px rgba(0,0,0,0.07), 0 2px 4px rgba(0,0,0,0.05);
}
```

**Typography:**
```css
body { font-family: 'Inter', 'Segoe UI', system-ui, -apple-system, sans-serif; }
```
Import Inter from Google Fonts: `https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700&display=swap`

**Design Principles:**
- Clean white surfaces with subtle shadows
- 8px border-radius on all cards
- `--primary` blue for interactive elements and accents
- No thick borders — use elevation via shadow
- Responsive CSS Grid layout

### Layout

```
┌─────────────────────────────────────────────────────┐
│  Header: --primary background                        │
│  "[Name]'s Dashboard" + Date + Source tags           │
│  [REFRESH] button + live clock                       │
├──────────────┬──────────────┬──────────────┬─────────┤
│  KPI: Action │  KPI: High   │  KPI: Slacks │  KPI:   │
│  Items       │  Priority    │  Sent        │  Emails  │
├──────────────┴──────────────┴──────────────┴─────────┤
│                              │                        │
│  ACTION ITEMS (main col)     │  ACTIVE DOCS (sidebar) │
│  - Filter buttons + ADD TASK │                        │
│  - Priority groups           │                        │
│  - Checkboxes                │                        │
│                              │                        │
├──────────────────────────────┴────────────────────────┤
│  DRAFT REPLIES                                        │
├───────────────────────────────────────────────────────┤
│  EMAILS NEEDING ATTENTION                             │
├───────────────────────────────────────────────────────┤
│  CHARTS: Priority breakdown + Source breakdown        │
└───────────────────────────────────────────────────────┘
```

### Key CSS

```css
/* Cards */
.card { background: var(--surface); border-radius: var(--radius); box-shadow: var(--shadow); border: 1px solid var(--border); }

/* KPI Cards */
.kpi-card { padding: 20px 24px; border-top: 4px solid var(--primary); }
.kpi-value { font-size: 42px; font-weight: 700; color: var(--dark); line-height: 1; }
.kpi-label { font-size: 12px; text-transform: uppercase; letter-spacing: 0.5px; color: var(--text-muted); margin-top: 4px; }
.kpi-card.high { border-top-color: var(--high); }
.kpi-card.medium { border-top-color: var(--medium); }

/* Action Items */
.action-item { background: var(--surface); border-radius: var(--radius); border: 1px solid var(--border); border-left: 6px solid var(--low); box-shadow: var(--shadow); padding: 14px 16px; display: flex; align-items: flex-start; gap: 12px; transition: box-shadow 0.15s ease; }
.action-item:hover { box-shadow: var(--shadow-md); }
.action-item[data-priority="high"] { border-left-color: var(--high); }
.action-item[data-priority="medium"] { border-left-color: var(--medium); }
.action-item.done { display: none; }

/* Source badges */
.badge { font-size: 11px; font-weight: 600; padding: 2px 8px; border-radius: 4px; text-transform: uppercase; letter-spacing: 0.3px; }
.badge-slack { background: #EEF2FF; color: #4338CA; }
.badge-email { background: #FEF3C7; color: #92400E; }
.badge-docs { background: #ECFDF5; color: #065F46; }

/* Filter buttons */
.filter-bar { display: flex; gap: 8px; flex-wrap: wrap; margin-bottom: 16px; }
.filter-btn { font-family: inherit; font-size: 13px; font-weight: 500; padding: 6px 14px; border: 1px solid var(--border); border-radius: 6px; background: var(--surface); cursor: pointer; transition: all 0.15s; }
.filter-btn:hover { background: var(--bg); }
.filter-btn.active { background: var(--primary); color: white; border-color: var(--primary); }
.filter-btn.add-task { background: #FBBF24; color: var(--dark); border-color: #F59E0B; margin-left: auto; font-weight: 600; }

/* Header */
.header { background: var(--primary); color: white; padding: 24px 32px; }
.header-title { font-size: 1.75rem; font-weight: 700; }
.header-subtitle { opacity: 0.7; font-size: 14px; margin-top: 4px; }

/* Draft replies */
.draft-item { background: var(--surface); border: 1px solid var(--border); border-left: 4px solid var(--primary); border-radius: var(--radius); padding: 16px; margin-bottom: 12px; }
.draft-text-box { background: var(--bg); border: 1px solid var(--border); border-radius: 6px; padding: 12px; font-size: 14px; line-height: 1.6; margin: 10px 0; color: var(--text); }
.draft-btn { font-family: inherit; font-size: 13px; font-weight: 600; padding: 6px 14px; border-radius: 6px; cursor: pointer; border: 1px solid var(--border); background: var(--surface); }
.draft-btn.open { background: var(--primary); color: white; border-color: var(--primary); text-decoration: none; display: inline-block; }
.draft-btn.dismiss { color: var(--text-muted); }

/* Tabs */
.page-tabs { display: flex; gap: 0; border-bottom: 2px solid var(--border); }
.page-tab { font-family: inherit; font-size: 14px; font-weight: 600; padding: 12px 24px; border: none; background: none; cursor: pointer; color: var(--text-muted); border-bottom: 2px solid transparent; margin-bottom: -2px; transition: all 0.15s; }
.page-tab.active { color: var(--primary); border-bottom-color: var(--primary); }
.page-tab .tab-badge { background: var(--primary); color: white; font-size: 11px; padding: 2px 7px; border-radius: 10px; margin-left: 6px; }
.tab-content { display: none; }
.tab-content.active { display: block; }
```

### Completing Animation & Persistent State

```css
.action-item.completing { animation: taskSlide 0.4s ease forwards; }
@keyframes taskSlide { to { opacity: 0; transform: translateX(20px); max-height: 0; padding: 0; margin: 0; overflow: hidden; } }
.draft-item.dismissing { animation: fadeOut 0.3s ease forwards; }
@keyframes fadeOut { to { opacity: 0; max-height: 0; padding: 0; overflow: hidden; } }
```

All state (completed items, dismissed drafts, custom tasks) persists indefinitely in `localStorage` under key `comms-dashboard-state`. See JavaScript section below.

### Refresh Button

```html
<button class="refresh-btn" id="refreshBtn" onclick="refreshDashboard()">
  <span id="refreshIcon">↻</span> Refresh
</button>
```

```javascript
function refreshDashboard() {
  const btn = document.getElementById('refreshBtn');
  btn.disabled = true;
  document.getElementById('refreshIcon').style.animation = 'spin 0.8s linear infinite';
  setTimeout(() => location.reload(), 800);
}
```

---

## Step 5B — Build the Creative Dashboard

Use this track when the user chose Creative or signaled a fun/expressive preference.

### Memphis Design System

**Colors:**

| Name | Hex | Usage |
|------|-----|-------|
| Hot Pink | `#FF6B9D` | Header background, primary accent |
| Dark Navy | `#1A1A2E` | Borders, dark backgrounds, text |
| Yellow | `#FFD93D` | Geometric shapes, highlights, tarot |
| Coral | `#FF6B6B` | High priority |
| Mint | `#55E6C1` | Docs, success states |
| Lavender | `#A29BFE` | Slack source, draft replies |
| Amber | `#F5A623` | Medium priority |
| Gray | `#8C8C8C` | Low priority, muted text |
| Cream | `#FFF5EE` | Page background |

**Typography:**
```css
@import url('https://fonts.googleapis.com/css2?family=Fredoka+One&family=Space+Grotesk:wght@400;500;600;700&display=swap');
```
- Display/Headers: `'Fredoka One', cursive` with `text-shadow: 3px 3px 0 #1A1A2E`
- Body: `'Space Grotesk', sans-serif`
- Labels: Space Grotesk, 11px uppercase, `letter-spacing: 1.5px`, weight 700

**Design Principles:**
- Thick black borders: `3px solid #1A1A2E`
- Sharp corners — no border-radius
- Solid offset shadows on hover: `box-shadow: -6px 6px 0 COLOR`
- Saturated solid-color backgrounds on KPI cards
- Geometric decorative elements: yellow diamond, mint circle

### Layout

```
┌──────────────────────────────────────────────────────┐
│  Header: Hot Pink + geometric shapes                  │
│  Title (Fredoka One) + Date + Live Clock              │
│  [REFRESH] button                                     │
├──────────────┬──────────────┬──────────────┬──────────┤
│  KPI: YELLOW │  KPI: CORAL  │  KPI: TEAL   │  KPI:   │
│  Action Items│  High Pri    │  Slacks Sent │  Emails  │
├──────────────┴──────────────┴──────────────┴──────────┤
│                              │                         │
│  ACTION ITEMS (left col)     │  TAROT CARD (right col) │
│  - Dark section bar          │  + DRAFT REPLIES below  │
│  - Filter buttons            │                         │
│  - Priority banners          │                         │
│  - Items with colored left   │                         │
│    borders + hover animation │                         │
├──────────────────────────────┴─────────────────────────┤
│  ACTIVE DOCS (full width, mint background)             │
├────────────────────────────────────────────────────────┤
│  EMAILS NEEDING ATTENTION (full width)                 │
├────────────────────────────────────────────────────────┤
│  CHARTS: Priority + Source breakdowns                  │
└────────────────────────────────────────────────────────┘
```

### Memphis Key CSS

```css
/* Action items — colored left border + hover shadow by source */
.action-item { border: 3px solid #1A1A2E; border-left: 7px solid #FF6B9D; background: white; transition: transform 0.2s, box-shadow 0.2s; display: flex; align-items: flex-start; gap: 12px; padding: 14px 16px; }
.action-item:hover { transform: translateX(6px) translateY(-2px); box-shadow: -6px 6px 0 #1A1A2E; }
.action-item[data-source="email"] { border-left-color: #FF6B6B; }
.action-item[data-source="slack"] { border-left-color: #A29BFE; }
.action-item[data-source="docs"] { border-left-color: #55E6C1; }
.action-item:hover[data-source="email"] { box-shadow: -6px 6px 0 #FF6B6B; }
.action-item:hover[data-source="slack"] { box-shadow: -6px 6px 0 #A29BFE; }
.action-item:hover[data-source="docs"] { box-shadow: -6px 6px 0 #55E6C1; }
.action-item.done { display: none; }

/* Section bar */
.section-bar { background: #1A1A2E; color: white; padding: 10px 20px; font-family: 'Fredoka One', cursive; font-size: 18px; letter-spacing: 1.5px; display: flex; align-items: center; gap: 10px; margin-bottom: 0; }
.diamond { width: 12px; height: 12px; background: #FFD93D; transform: rotate(45deg); flex-shrink: 0; }

/* KPI cards */
.kpi-card { border: 3px solid #1A1A2E; padding: 20px; }
.kpi-value { font-family: 'Fredoka One', cursive; font-size: 48px; color: #1A1A2E; line-height: 1; }
.kpi-label { font-family: 'Space Grotesk', sans-serif; font-size: 11px; font-weight: 700; text-transform: uppercase; letter-spacing: 1.5px; color: #1A1A2E; margin-top: 4px; }
.kpi-grid { display: grid; grid-template-columns: repeat(4, 1fr); gap: 0; }
.kpi-card:nth-child(1) { background: #FFD93D; }
.kpi-card:nth-child(2) { background: #FF6B6B; color: white; }
.kpi-card:nth-child(3) { background: #55E6C1; }
.kpi-card:nth-child(4) { background: #A29BFE; }

/* Header */
.header { background: #FF6B9D; padding: 24px 32px; position: relative; overflow: hidden; }
.header::before { content: ''; position: absolute; top: 15px; right: 40px; width: 50px; height: 50px; background: #FFD93D; transform: rotate(45deg); border: 3px solid #1A1A2E; }
.header::after { content: ''; position: absolute; top: 60px; right: 110px; width: 25px; height: 25px; border-radius: 50%; background: #55E6C1; border: 3px solid #1A1A2E; }
.header-title { font-family: 'Fredoka One', cursive; font-size: 2rem; color: white; text-shadow: 3px 3px 0 #1A1A2E; position: relative; z-index: 2; }

/* Two-column layout */
.action-tarot-layout { display: grid; grid-template-columns: 1fr 380px; gap: 24px; margin-bottom: 30px; align-items: start; }
.tarot-col { position: sticky; top: 20px; }

/* Tarot card */
.tarot-card { background: #1A1A2E; border: 3px solid #1A1A2E; padding: 4px; }
.tarot-inner { border: 3px solid #FFD93D; padding: 20px; text-align: center; position: relative; }
.tarot-inner::before, .tarot-inner::after { content: '\2726'; position: absolute; top: 10px; color: #FFD93D; font-size: 18px; }
.tarot-inner::before { left: 10px; }
.tarot-inner::after { right: 10px; }
.tarot-title { font-family: 'Fredoka One', cursive; color: #FF6B9D; font-size: 26px; margin-bottom: 6px; }
.tarot-meaning { color: #C4DBFF; font-size: 14px; line-height: 1.6; font-style: italic; margin-bottom: 16px; }
.tarot-keyword { color: #FFD93D; font-weight: 700; font-size: 12px; text-transform: uppercase; letter-spacing: 1px; padding: 4px 10px; border: 1px solid #FFD93D; display: inline-block; margin: 3px; }

/* Completing & dismissing animations */
.action-item.completing { animation: taskSlide 0.5s ease forwards; overflow: hidden; }
@keyframes taskSlide { 0% { opacity: 1; transform: translateX(0); } 50% { opacity: 0.5; transform: translateX(20px); } 100% { opacity: 0; max-height: 0; padding: 0; margin: 0; transform: translateX(40px); } }
.draft-item.dismissing { animation: fadeOut 0.35s ease forwards; }
@keyframes fadeOut { to { opacity: 0; max-height: 0; padding: 0; overflow: hidden; } }

/* Toast */
#toast { position: fixed; bottom: 24px; right: 24px; background: #55E6C1; color: #1A1A2E; font-family: 'Fredoka One', cursive; font-size: 15px; padding: 12px 28px; border: 3px solid #1A1A2E; z-index: 9999; opacity: 0; transition: opacity 0.3s; pointer-events: none; }
#toast.show { opacity: 1; }
```

### Tarot Card of the Day

The tarot card is generated from a full 78-card dataset embedded directly in the HTML as a JavaScript constant. This makes the dashboard fully self-contained — no external JSON file needed.

**Selection logic:** Use the day of year to deterministically select a card that rotates through all 78.

```javascript
const TAROT_CARDS = [
  // 22 MAJOR ARCANA
  { name: "The Fool", numeral: "0", suit: "major", meaning: "You stand at the threshold, unburdened by what you think you should know. The Fool's journey begins not with certainty but with the willingness to leap toward what calls to you. Your naivety is not a weakness—it's your freedom. Trust the path beneath your feet, even when you can't see where it leads.", keywords: ["new beginnings", "taking risks", "faith", "innocence"], luckyColor: { name: "Mint Green", hex: "#55E6C1" }, luckyNumber: 1, emoji: "🃏" },
  { name: "The Magician", numeral: "I", suit: "major", meaning: "You have everything you need. The Magician holds the four elements in their hands, a reminder that you're already in possession of your own power. This is not about conjuring illusions but about conscious intention. What you focus on, you magnetize. Act as if you already know your worth.", keywords: ["manifestation", "resourcefulness", "power", "inspired action"], luckyColor: { name: "Yellow", hex: "#FFD93D" }, luckyNumber: 13, emoji: "🪄" },
  { name: "The High Priestess", numeral: "II", suit: "major", meaning: "The answers you seek live in the spaces between knowing and not-knowing. She invites you into the silence, into the realm of intuition and hidden things. You are wiser than you give yourself credit for. Stop asking everyone else for permission to trust what you already feel.", keywords: ["intuition", "sacred knowledge", "mystery", "the subconscious"], luckyColor: { name: "Lavender", hex: "#A29BFE" }, luckyNumber: 27, emoji: "🌙" },
  { name: "The Empress", numeral: "III", suit: "major", meaning: "Abundance flows through you when you tend to what matters. The Empress is embodied creativity, nourishment, and the generative power of claiming space. You have permission to create, to grow, to take up room. Your presence, your gifts, your fullness — they are not too much.", keywords: ["fertility", "abundance", "nurturing", "creative power"], luckyColor: { name: "Coral", hex: "#FF6B6B" }, luckyNumber: 41, emoji: "👑" },
  { name: "The Emperor", numeral: "IV", suit: "major", meaning: "You are being called to claim your authority with integrity. The Emperor doesn't lead through domination but through clear boundaries and earned respect. This is about sovereignty — the power to direct your own life. Set the rules that serve you. Build structures that hold your vision.", keywords: ["authority", "leadership", "structure", "control"], luckyColor: { name: "Navy", hex: "#1A1A2E" }, luckyNumber: 8, emoji: "🏛️" },
  { name: "The Hierophant", numeral: "V", suit: "major", meaning: "There is wisdom in tradition — and wisdom in knowing when to question it. The Hierophant asks you to examine what you have been taught versus what you actually believe. Find the teachers who have genuinely earned your trust. Be discerning about who you let shape your understanding.", keywords: ["tradition", "spiritual wisdom", "institutions", "mentorship"], luckyColor: { name: "Amber", hex: "#F5A623" }, luckyNumber: 16, emoji: "🔑" },
  { name: "The Lovers", numeral: "VI", suit: "major", meaning: "This is a card of alignment, not just romance. The Lovers asks: are your choices in integrity with your values? When you choose from your authentic self rather than from fear or obligation, you create the conditions for genuine connection — with others and with your own life's purpose.", keywords: ["love", "alignment", "values", "choice"], luckyColor: { name: "Hot Pink", hex: "#FF6B9D" }, luckyNumber: 22, emoji: "💕" },
  { name: "The Chariot", numeral: "VII", suit: "major", meaning: "You have what it takes to move forward even when the forces around you seem contradictory. The Chariot is disciplined momentum — harnessing opposing energies into forward motion. Victory comes not from forcing your will but from mastering your own impulses. Keep your eyes on where you're headed.", keywords: ["determination", "victory", "willpower", "momentum"], luckyColor: { name: "Mint", hex: "#55E6C1" }, luckyNumber: 7, emoji: "🏆" },
  { name: "Strength", numeral: "VIII", suit: "major", meaning: "True strength is patient, compassionate, and quietly powerful. This card shows us that courage isn't the absence of fear but the decision to act from love anyway. You are stronger than the forces that try to diminish you. Lead with your heart and watch what becomes possible.", keywords: ["courage", "patience", "compassion", "inner strength"], luckyColor: { name: "Coral", hex: "#FF6B6B" }, luckyNumber: 3, emoji: "🦁" },
  { name: "The Hermit", numeral: "IX", suit: "major", meaning: "This is a time for solitude, reflection, and inner guidance. The Hermit carries a lantern not to show others the way, but to illuminate the next step on their own path. You have the answers you're looking for. The wisdom you need lives inside you — quiet yourself enough to hear it.", keywords: ["solitude", "introspection", "guidance", "wisdom"], luckyColor: { name: "Gray", hex: "#8C8C8C" }, luckyNumber: 9, emoji: "🔦" },
  { name: "Wheel of Fortune", numeral: "X", suit: "major", meaning: "Change is the only constant — and this wheel is always turning. The Wheel of Fortune reminds us that we are never permanently at the top or the bottom. What rises falls; what falls will rise. Work with cycles rather than against them. Trust that life is moving in your favor even when you can't see it yet.", keywords: ["cycles", "fate", "turning points", "luck"], luckyColor: { name: "Yellow", hex: "#FFD93D" }, luckyNumber: 10, emoji: "🎡" },
  { name: "Justice", numeral: "XI", suit: "major", meaning: "Justice asks for radical accountability — not punishment, but clarity. What is actually true here? What do you actually want? This card strips away illusion and asks you to see things as they are, not as you fear them to be or wish they were. When you act from truth, you create alignment.", keywords: ["fairness", "truth", "accountability", "balance"], luckyColor: { name: "Lavender", hex: "#A29BFE" }, luckyNumber: 12, emoji: "⚖️" },
  { name: "The Hanged Man", numeral: "XII", suit: "major", meaning: "The wisdom of pause. The Hanged Man suspends action voluntarily, choosing a different vantage point from which to see. Things look very different upside down. What if the delay, the waiting, the stuck feeling is actually a gift of perspective? What do you see when you stop trying to force an outcome?", keywords: ["surrender", "new perspective", "pause", "letting go"], luckyColor: { name: "Mint", hex: "#55E6C1" }, luckyNumber: 33, emoji: "🙃" },
  { name: "Death", numeral: "XIII", suit: "major", meaning: "This is the card of profound transformation — not endings, but evolution. What is dying in your life right now? What has run its course and is ready to be released? Death clears the way for what wants to grow. You cannot hold onto the old form and welcome the new. Let it go.", keywords: ["transformation", "endings", "transition", "rebirth"], luckyColor: { name: "Navy", hex: "#1A1A2E" }, luckyNumber: 13, emoji: "🦋" },
  { name: "Temperance", numeral: "XIV", suit: "major", meaning: "Integration is the work. Temperance asks you to blend seemingly opposing forces into something whole — patience and urgency, strength and softness, solitude and connection. This card is the alchemist's art: nothing wasted, everything purposeful. Your healing is happening even when you can't see it.", keywords: ["balance", "alchemy", "patience", "integration"], luckyColor: { name: "Mint", hex: "#55E6C1" }, luckyNumber: 14, emoji: "⚗️" },
  { name: "The Devil", numeral: "XV", suit: "major", meaning: "What binds you? The Devil illuminates our attachments — to patterns, to comfort, to relationships that no longer serve us. The chains are often looser than they appear. This card asks you to look clearly at what you're complicit in. You have more agency than you think. And liberation begins with honesty.", keywords: ["shadow", "attachment", "liberation", "illusion"], luckyColor: { name: "Coral", hex: "#FF6B6B" }, luckyNumber: 15, emoji: "🔗" },
  { name: "The Tower", numeral: "XVI", suit: "major", meaning: "The structures built on false foundations cannot stand. The Tower feels like chaos — sudden, disorienting, disruptive. But what looks like destruction is also revelation. What falls away was never as solid as it seemed. When the dust settles, you will see more clearly. Trust that what remains is real.", keywords: ["disruption", "revelation", "sudden change", "breakthrough"], luckyColor: { name: "Amber", hex: "#F5A623" }, luckyNumber: 16, emoji: "⚡" },
  { name: "The Star", numeral: "XVII", suit: "major", meaning: "After the storm, hope. The Star pours healing waters with quiet confidence — one vessel into the earth, one into the water, nourishing both body and soul. Your healing is not contingent on everything being okay. You can be replenished even now. Let hope in. Let yourself be seen.", keywords: ["hope", "healing", "inspiration", "renewal"], luckyColor: { name: "Lavender", hex: "#A29BFE" }, luckyNumber: 17, emoji: "⭐" },
  { name: "The Moon", numeral: "XVIII", suit: "major", meaning: "Not everything can be seen clearly by moonlight — and that's the point. The Moon rules the realm of dreams, illusions, and what we sense but cannot verify. This is a time to pay attention to your intuition even (especially) when logic contradicts it. Fear is a messenger. What is it telling you?", keywords: ["intuition", "illusion", "the unconscious", "fear"], luckyColor: { name: "Navy", hex: "#1A1A2E" }, luckyNumber: 29, emoji: "🌕" },
  { name: "The Sun", numeral: "XIX", suit: "major", meaning: "Joy is your birthright. The Sun brings clarity, vitality, and the kind of confidence that doesn't need to prove itself. You are seen. You are radiant. Whatever obscured your light is moving. Let yourself be happy. Let yourself be celebrated. This is a moment of genuine, earned brightness — receive it fully.", keywords: ["joy", "success", "clarity", "vitality"], luckyColor: { name: "Yellow", hex: "#FFD93D" }, luckyNumber: 19, emoji: "☀️" },
  { name: "Judgement", numeral: "XX", suit: "major", meaning: "A calling is sounding. Judgement is the moment of awakening — when we hear the call of our truest purpose and are asked to rise to meet it. This is not about being judged by others but about how you judge yourself. Can you forgive yourself enough to step fully into who you are becoming?", keywords: ["reckoning", "awakening", "forgiveness", "calling"], luckyColor: { name: "Hot Pink", hex: "#FF6B9D" }, luckyNumber: 20, emoji: "📯" },
  { name: "The World", numeral: "XXI", suit: "major", meaning: "Completion, integration, wholeness. The World arrives when a significant cycle closes and you can finally see the full arc of what you've lived through. You have earned this. The wisdom you carry now cannot be taken from you. Celebrate what you've built — and know that the next Fool's journey is already calling.", keywords: ["completion", "integration", "accomplishment", "wholeness"], luckyColor: { name: "Mint", hex: "#55E6C1" }, luckyNumber: 21, emoji: "🌍" },
  // 14 WANDS
  { name: "Ace of Wands", numeral: "Ace", suit: "wands", meaning: "A spark is igniting. The Ace of Wands brings new creative fire, inspiration that demands expression. You're being offered a gift of passion and possibility. Don't overthink it. Feel the heat, follow the impulse, and let your creative force move you. This is permission to want something, create something, become something new.", keywords: ["inspiration", "creative spark", "potential", "new passion"], luckyColor: { name: "Amber", hex: "#F5A623" }, luckyNumber: 11, emoji: "🌱" },
  { name: "Two of Wands", numeral: "2", suit: "wands", meaning: "You hold your own power in your hands and a world of possibility ahead. The Two of Wands asks: what do you want to build? You have vision and resources — now comes the planning, the choosing, the commitment. Don't get stuck in dreaming. Move from intention toward concrete action. The world is waiting.", keywords: ["planning", "decision", "power", "potential"], luckyColor: { name: "Amber", hex: "#F5A623" }, luckyNumber: 55, emoji: "🧭" },
  { name: "Three of Wands", numeral: "3", suit: "wands", meaning: "Your vision is expanding. The Three of Wands speaks of growth, of your projects ripening, of collaborations that multiply your reach. You're building something larger than yourself. Stay grounded even as you dream bigger. The momentum is real, but you must tend to it. Keep your eyes on the horizon while your feet stay planted.", keywords: ["expansion", "growth", "foresight", "collaboration"], luckyColor: { name: "Amber", hex: "#F5A623" }, luckyNumber: 20, emoji: "🚀" },
  { name: "Four of Wands", numeral: "4", suit: "wands", meaning: "Celebration is earned and necessary. The Four of Wands marks a pause for joy, for harvest, for acknowledging what you've built. This is your moment to witness your own progress. Gather with those who matter. Rejoice in the foundation you've laid. You deserve this rest, this recognition.", keywords: ["celebration", "community", "joy", "stability"], luckyColor: { name: "Hot Pink", hex: "#FF6B9D" }, luckyNumber: 69, emoji: "🎉" },
  { name: "Five of Wands", numeral: "5", suit: "wands", meaning: "Conflict is here, and it's not always bad. The Five of Wands shows friction, competing desires, perspectives clashing. Rather than avoid this, engage with it consciously. What are you fighting for? What needs to be resolved? This tension contains information. Move through it with awareness instead of reactivity.", keywords: ["conflict", "competition", "friction", "perspective"], luckyColor: { name: "Coral", hex: "#FF6B6B" }, luckyNumber: 31, emoji: "💥" },
  { name: "Six of Wands", numeral: "6", suit: "wands", meaning: "You've earned this recognition. The Six of Wands is the victory lap, the moment when your efforts are publicly acknowledged. Don't deflect the praise or minimize what you've accomplished. Let yourself be seen in your success. This win belongs to you — claim it, receive it, let it fortify you for what comes next.", keywords: ["victory", "recognition", "confidence", "success"], luckyColor: { name: "Yellow", hex: "#FFD93D" }, luckyNumber: 6, emoji: "🏅" },
  { name: "Seven of Wands", numeral: "7", suit: "wands", meaning: "Hold your ground. The Seven of Wands finds you at a high point, defending the position you've earned. Others may challenge you, question you, push back. But you got here through real work. Stand in what you know. You don't need to justify your success to everyone who didn't achieve it.", keywords: ["perseverance", "defense", "conviction", "courage"], luckyColor: { name: "Amber", hex: "#F5A623" }, luckyNumber: 47, emoji: "🛡️" },
  { name: "Eight of Wands", numeral: "8", suit: "wands", meaning: "Things are moving fast. The Eight of Wands is swift communication, rapid developments, momentum that's almost electric. This is not a time to slow down or second-guess. Stay focused, be decisive, and trust that the velocity is leading somewhere. Clear the runway for what's incoming.", keywords: ["speed", "momentum", "swift action", "communication"], luckyColor: { name: "Mint", hex: "#55E6C1" }, luckyNumber: 8, emoji: "⚡" },
  { name: "Nine of Wands", numeral: "9", suit: "wands", meaning: "You are exhausted but not defeated. The Nine of Wands honors how far you've come — through challenges that would have stopped many others. You're still standing. The finish line is close. Rest if you need to, but don't give up now. You have more reserves than you think. Keep going.", keywords: ["resilience", "persistence", "courage", "boundaries"], luckyColor: { name: "Amber", hex: "#F5A623" }, luckyNumber: 9, emoji: "🩹" },
  { name: "Ten of Wands", numeral: "10", suit: "wands", meaning: "You're carrying too much. The Ten of Wands arrives when the burden has become heavier than it needs to be — when the drive that got you here is now weighing you down. What can you put down? What were you never supposed to carry alone? Delegation is not weakness. It's wisdom.", keywords: ["burden", "overextension", "responsibility", "delegation"], luckyColor: { name: "Gray", hex: "#8C8C8C" }, luckyNumber: 10, emoji: "🎒" },
  { name: "Page of Wands", numeral: "Page", suit: "wands", meaning: "Your curiosity is alive. The Page of Wands brings enthusiasm, wonder, and the hunger to learn and create. You're discovering your voice and your power. Don't let anyone convince you to play small. Follow what excites you. Your fresh perspective and raw passion are exactly what's needed.", keywords: ["curiosity", "enthusiasm", "potential", "discovery"], luckyColor: { name: "Amber", hex: "#F5A623" }, luckyNumber: 5, emoji: "🧑‍🔥" },
  { name: "Knight of Wands", numeral: "Knight", suit: "wands", meaning: "You are a force in motion. The Knight of Wands charges forward with infectious confidence and creative fire. Your passion is magnetic and your timing, when you trust it, is impeccable. Watch only for recklessness — not every battle deserves your full cavalry. Channel the fire; don't let it burn everything down.", keywords: ["passion", "adventure", "impulsiveness", "confidence"], luckyColor: { name: "Coral", hex: "#FF6B6B" }, luckyNumber: 17, emoji: "🏇" },
  { name: "Queen of Wands", numeral: "Queen", suit: "wands", meaning: "You are magnetic. The Queen of Wands leads with warmth, creativity, and an unshakeable sense of self. She doesn't ask permission to take up space — she creates it. You are being called to step into your full creative authority. Your confidence inspires others. Your fire lights the room.", keywords: ["charisma", "courage", "creativity", "independence"], luckyColor: { name: "Hot Pink", hex: "#FF6B9D" }, luckyNumber: 23, emoji: "👸‍🔥" },
  { name: "King of Wands", numeral: "King", suit: "wands", meaning: "Vision and the power to realize it. The King of Wands is an inspired leader who moves through the world with authority and warmth. You are being called to lead — not by controlling, but by energizing. Your boldness gives others permission to be bold. Show the way forward by walking it yourself.", keywords: ["vision", "leadership", "boldness", "generosity"], luckyColor: { name: "Yellow", hex: "#FFD93D" }, luckyNumber: 4, emoji: "👑🔥" },
  // 14 CUPS
  { name: "Ace of Cups", numeral: "Ace", suit: "cups", meaning: "An opening in your heart. The Ace of Cups offers the beginning of something emotionally rich — love, creativity, spiritual connection, compassion. Receive it. You are worthy of this overflow. Let yourself feel without censoring. The heart that can feel deeply is the heart that can also love deeply.", keywords: ["new love", "emotional beginning", "intuition", "creativity"], luckyColor: { name: "Lavender", hex: "#A29BFE" }, luckyNumber: 2, emoji: "💧" },
  { name: "Two of Cups", numeral: "2", suit: "cups", meaning: "Partnership and mutual recognition. The Two of Cups is connection that feels rare — when two people truly see each other. This doesn't have to be romantic. It can be a collaboration, a friendship, an alliance built on genuine respect. Honor what you're building with this person. It is precious.", keywords: ["partnership", "connection", "mutual respect", "attraction"], luckyColor: { name: "Hot Pink", hex: "#FF6B9D" }, luckyNumber: 22, emoji: "🥂" },
  { name: "Three of Cups", numeral: "3", suit: "cups", meaning: "Community, celebration, and the joy of chosen family. The Three of Cups invites you to gather with people who genuinely celebrate you — not just tolerate you. This is the card of friendship, of shared abundance, of lifting each other up. Who in your life deserves more of your appreciation right now?", keywords: ["friendship", "celebration", "community", "abundance"], luckyColor: { name: "Mint", hex: "#55E6C1" }, luckyNumber: 3, emoji: "🎊" },
  { name: "Four of Cups", numeral: "4", suit: "cups", meaning: "You may be so focused on what's missing that you're overlooking what's being offered. The Four of Cups is the card of emotional withdrawal, of apathy or discontent. Something new is being extended to you. Open your eyes. Your dissatisfaction is valid — but it may also be blinding you to possibility.", keywords: ["apathy", "introspection", "new opportunity", "reevaluation"], luckyColor: { name: "Gray", hex: "#8C8C8C" }, luckyNumber: 4, emoji: "🙈" },
  { name: "Five of Cups", numeral: "5", suit: "cups", meaning: "Grief is real, and it asks to be honored. The Five of Cups mourns what has been lost — genuinely, without bypassing. But look: behind the spilled cups, two remain upright. There is still something intact. When you are ready, turn toward what remains. The path continues from here.", keywords: ["loss", "grief", "regret", "recovery"], luckyColor: { name: "Navy", hex: "#1A1A2E" }, luckyNumber: 5, emoji: "😢" },
  { name: "Six of Cups", numeral: "6", suit: "cups", meaning: "Nostalgia, gifts, and the sweetness of innocence remembered. The Six of Cups returns you to something pure — a memory, a simpler time, a generous impulse. This card asks: where do you need to bring more innocence, more play, more genuine generosity? The past can be a resource, not just a place you were.", keywords: ["nostalgia", "childhood", "generosity", "innocence"], luckyColor: { name: "Lavender", hex: "#A29BFE" }, luckyNumber: 6, emoji: "🌸" },
  { name: "Seven of Cups", numeral: "7", suit: "cups", meaning: "So many options — and yet none of them feel quite right because you haven't chosen yet. The Seven of Cups is the card of fantasy, of overwhelm, of beautiful possibilities that distract more than they clarify. What do you actually want? Not what looks good on paper. What, if you achieved it, would genuinely satisfy?", keywords: ["fantasy", "illusion", "choices", "wishful thinking"], luckyColor: { name: "Lavender", hex: "#A29BFE" }, luckyNumber: 7, emoji: "✨" },
  { name: "Eight of Cups", numeral: "8", suit: "cups", meaning: "You are leaving something behind — not because it's bad, but because it no longer holds what you need. The Eight of Cups is a conscious departure, a brave turning away toward something that calls more deeply. It takes courage to walk away from what you've invested in. That courage is yours.", keywords: ["withdrawal", "transition", "deeper meaning", "walking away"], luckyColor: { name: "Navy", hex: "#1A1A2E" }, luckyNumber: 29, emoji: "🚶" },
  { name: "Nine of Cups", numeral: "9", suit: "cups", meaning: "The wish card. The Nine of Cups is deep emotional satisfaction — the sense that life is good, that you are content, that your heart is full. This is not about having everything; it's about feeling genuinely grateful for what is. Let yourself be happy. You don't need to earn contentment.", keywords: ["contentment", "satisfaction", "gratitude", "wish fulfillment"], luckyColor: { name: "Yellow", hex: "#FFD93D" }, luckyNumber: 9, emoji: "🥰" },
  { name: "Ten of Cups", numeral: "10", suit: "cups", meaning: "Emotional wholeness, lasting joy, and the home you've made — inside yourself and with those you love. The Ten of Cups is the fulfillment of the heart's deepest longing: not perfection, but genuine belonging and peace. What does your version of this look like? You get to define what home means.", keywords: ["happiness", "harmony", "family", "alignment"], luckyColor: { name: "Hot Pink", hex: "#FF6B9D" }, luckyNumber: 10, emoji: "🏡" },
  { name: "Page of Cups", numeral: "Page", suit: "cups", meaning: "A message from your own depths. The Page of Cups is the inner child, the dreamer, the one who still believes in magic. She brings unexpected news, creative inspiration, and a reminder that the emotional life has its own intelligence. Listen to what you feel, even when it doesn't make logical sense.", keywords: ["creativity", "intuition", "emotional messages", "wonder"], luckyColor: { name: "Lavender", hex: "#A29BFE" }, luckyNumber: 11, emoji: "🐠" },
  { name: "Knight of Cups", numeral: "Knight", suit: "cups", meaning: "A romantic idealist in motion. The Knight of Cups follows the heart with graceful determination — pursuing beauty, love, and meaning with earnest devotion. This is the knight who brings proposals, who shows up with genuine feeling. But watch for the tendency toward fantasy. Make sure the dream connects to reality.", keywords: ["romance", "charm", "idealism", "following the heart"], luckyColor: { name: "Hot Pink", hex: "#FF6B9D" }, luckyNumber: 14, emoji: "🏇💕" },
  { name: "Queen of Cups", numeral: "Queen", suit: "cups", meaning: "You lead from the depths of feeling. The Queen of Cups is attuned to emotional truth, to what lives beneath the surface. Her sensitivity is not weakness — it is her superpower. She holds space without dissolving into it. Practice being both soft and boundaried. Your empathy, at its best, changes everything around you.", keywords: ["empathy", "intuition", "emotional intelligence", "care"], luckyColor: { name: "Lavender", hex: "#A29BFE" }, luckyNumber: 12, emoji: "👸💧" },
  { name: "King of Cups", numeral: "King", suit: "cups", meaning: "Emotional mastery and compassionate authority. The King of Cups holds deep feeling without being ruled by it. He is steady, generous, wise — and he leads with his whole self, not just his intellect. You are being invited to bring this full-hearted leadership to your current situation. Feel it all, and then decide.", keywords: ["emotional maturity", "compassion", "diplomacy", "wisdom"], luckyColor: { name: "Mint", hex: "#55E6C1" }, luckyNumber: 3, emoji: "👑💙" },
  // 14 SWORDS
  { name: "Ace of Swords", numeral: "Ace", suit: "swords", meaning: "A breakthrough in clarity. The Ace of Swords cuts through confusion and offers you the truth you've been circling. This kind of clarity can feel sharp, even uncomfortable — but it is freeing. Name what is actually true. Say what actually needs to be said. The mind, at its best, is your ally.", keywords: ["clarity", "breakthrough", "truth", "new ideas"], luckyColor: { name: "Mint", hex: "#55E6C1" }, luckyNumber: 1, emoji: "⚡" },
  { name: "Two of Swords", numeral: "2", suit: "swords", meaning: "You're at a standstill — blindfolded, sword in hand, not yet ready to choose. The Two of Swords is the card of stalemate, of a decision being avoided. The delay is understandable. But eventually, you must look. You must remove the blindfold and face what you already sense is true.", keywords: ["indecision", "avoidance", "stalemate", "difficult choice"], luckyColor: { name: "Gray", hex: "#8C8C8C" }, luckyNumber: 2, emoji: "😶" },
  { name: "Three of Swords", numeral: "3", suit: "swords", meaning: "Heartbreak, grief, betrayal — this card does not flinch from pain. The Three of Swords says: yes, this hurts. Yes, it's real. And also: you will survive this. The heart can hold more than it thinks. Let yourself grieve without rushing the process. The rain will stop. The sky will clear.", keywords: ["heartbreak", "grief", "sorrow", "betrayal"], luckyColor: { name: "Navy", hex: "#1A1A2E" }, luckyNumber: 3, emoji: "💔" },
  { name: "Four of Swords", numeral: "4", suit: "swords", meaning: "Rest is not optional right now — it's necessary. The Four of Swords asks you to pause the battle, withdraw from the noise, and let your nervous system recover. You cannot pour from empty. Silence is productive. Sleep is productive. Recovery is how you prepare for what comes next.", keywords: ["rest", "recuperation", "silence", "contemplation"], luckyColor: { name: "Lavender", hex: "#A29BFE" }, luckyNumber: 4, emoji: "😴" },
  { name: "Five of Swords", numeral: "5", suit: "swords", meaning: "Not every battle is worth winning. The Five of Swords shows the hollow victory — the kind where you got what you wanted but lost something more important in the process. Or it shows the loss that, in retrospect, freed you. Examine the conflict you're in. Is winning this really what you want?", keywords: ["conflict", "defeat", "tension", "hollow victory"], luckyColor: { name: "Coral", hex: "#FF6B6B" }, luckyNumber: 5, emoji: "⚔️" },
  { name: "Six of Swords", numeral: "6", suit: "swords", meaning: "Moving into calmer waters. The Six of Swords is the card of transition — of leaving turbulence behind and heading toward something steadier. It may not be joyful yet; the grief of what you're leaving is still with you. But you are moving. The direction is toward healing. Trust the crossing.", keywords: ["transition", "moving on", "healing", "calmer waters"], luckyColor: { name: "Mint", hex: "#55E6C1" }, luckyNumber: 6, emoji: "🚣" },
  { name: "Seven of Swords", numeral: "7", suit: "swords", meaning: "Cunning, strategy, and the question of ethics. The Seven of Swords asks you to look honestly at where you may be cutting corners, avoiding confrontation, or operating in ways that feel slightly off. And it asks: who might be doing this to you? Be discerning. Protect what matters. And stay in your integrity.", keywords: ["strategy", "stealth", "deception", "cunning"], luckyColor: { name: "Amber", hex: "#F5A623" }, luckyNumber: 7, emoji: "🦊" },
  { name: "Eight of Swords", numeral: "8", suit: "swords", meaning: "The prison is largely constructed by your own mind. The Eight of Swords shows us bound and blindfolded, surrounded by swords that are not actually blocking the way out. The limitation is real — but it is smaller than it feels. What would you try if you knew the walls were less solid than they appear?", keywords: ["restriction", "fear", "self-imposed limits", "trapped thinking"], luckyColor: { name: "Gray", hex: "#8C8C8C" }, luckyNumber: 8, emoji: "🙈" },
  { name: "Nine of Swords", numeral: "9", suit: "swords", meaning: "The 3am card. The Nine of Swords is the anxiety that wakes you in the night — the worst-case scenarios, the spiral of worry. Your fears feel very real right now. But you've survived your darkest nights before. Talk to someone you trust. Let light in. The catastrophe your mind is constructing is not certain.", keywords: ["anxiety", "nightmares", "worry", "mental anguish"], luckyColor: { name: "Navy", hex: "#1A1A2E" }, luckyNumber: 9, emoji: "😰" },
  { name: "Ten of Swords", numeral: "10", suit: "swords", meaning: "This ending is final — and that finality is, in its own way, a mercy. The Ten of Swords is total collapse, bottoming out, the end of something that couldn't continue. It's painful. It's also clear. The only direction from here is up. The dawn is already beginning. Let this be over.", keywords: ["endings", "defeat", "rock bottom", "inevitable ending"], luckyColor: { name: "Navy", hex: "#1A1A2E" }, luckyNumber: 10, emoji: "🌅" },
  { name: "Page of Swords", numeral: "Page", suit: "swords", meaning: "Sharp-minded and hungry to understand. The Page of Swords brings a quick wit, a questioning nature, and the energy of someone who is not yet afraid to challenge the established order. Your mind is your greatest asset right now. Ask the hard questions. Follow the ideas that won't let you go.", keywords: ["curiosity", "wit", "communication", "mental agility"], luckyColor: { name: "Mint", hex: "#55E6C1" }, luckyNumber: 11, emoji: "🧠" },
  { name: "Knight of Swords", numeral: "Knight", suit: "swords", meaning: "Move fast, think clearly, be precise. The Knight of Swords charges into the fray with intellectual courage and decisive energy. This is the moment for bold thinking and swift action. But temper the urgency with enough care not to leave wreckage behind. Speed is your gift — thoughtlessness is the risk.", keywords: ["ambition", "speed", "decisiveness", "communication"], luckyColor: { name: "Coral", hex: "#FF6B6B" }, luckyNumber: 14, emoji: "🏇⚔️" },
  { name: "Queen of Swords", numeral: "Queen", suit: "swords", meaning: "She has been through the fire and came out clear. The Queen of Swords does not flinch from truth. She is direct, perceptive, and unapologetically herself — not from coldness but from earned wisdom. You are being asked to access this clarity now. Speak from your truth. See things as they are.", keywords: ["clarity", "directness", "independence", "honest wisdom"], luckyColor: { name: "Lavender", hex: "#A29BFE" }, luckyNumber: 12, emoji: "👸⚔️" },
  { name: "King of Swords", numeral: "King", suit: "swords", meaning: "Rational authority and the courage to hold a complex truth. The King of Swords thinks clearly, communicates precisely, and leads with principled decision-making. You are being asked to operate from this kind of high-integrity clarity — to see through sentiment to what is actually true and then act accordingly.", keywords: ["authority", "truth", "ethics", "clear thinking"], luckyColor: { name: "Navy", hex: "#1A1A2E" }, luckyNumber: 1, emoji: "👑⚔️" },
  // 14 PENTACLES
  { name: "Ace of Pentacles", numeral: "Ace", suit: "pentacles", meaning: "A tangible new beginning. The Ace of Pentacles brings an opportunity in the material world — a new venture, a financial opening, a chance to build something real. This is seed money for the life you want to grow. Receive it with intention. Plant carefully. Tend what you start.", keywords: ["new opportunity", "abundance", "manifestation", "prosperity"], luckyColor: { name: "Mint", hex: "#55E6C1" }, luckyNumber: 1, emoji: "🌿" },
  { name: "Two of Pentacles", numeral: "2", suit: "pentacles", meaning: "You're juggling, and somehow managing to keep everything in the air. The Two of Pentacles is the card of balance amid complexity — multiple responsibilities, shifting priorities, the art of adaptation. You're more capable than you know. Just don't let the performance of balance substitute for actually taking care of yourself.", keywords: ["balance", "adaptability", "time management", "flexibility"], luckyColor: { name: "Amber", hex: "#F5A623" }, luckyNumber: 2, emoji: "🤹" },
  { name: "Three of Pentacles", numeral: "3", suit: "pentacles", meaning: "Collaboration, craft, and the satisfaction of building something together. The Three of Pentacles honors the work of skilled people who bring complementary strengths to a shared vision. You don't have to do this alone. In fact, the work becomes better when you don't. Who do you need on your team?", keywords: ["teamwork", "craft", "collaboration", "skill"], luckyColor: { name: "Mint", hex: "#55E6C1" }, luckyNumber: 3, emoji: "🏗️" },
  { name: "Four of Pentacles", numeral: "4", suit: "pentacles", meaning: "Hold on — but not too tightly. The Four of Pentacles knows the value of security and the fear of loss. There is wisdom in protecting what you've built. But when holding on becomes hoarding, when security becomes control, something essential is lost. What are you gripping that needs to breathe?", keywords: ["security", "control", "conservation", "materialism"], luckyColor: { name: "Amber", hex: "#F5A623" }, luckyNumber: 4, emoji: "🔒" },
  { name: "Five of Pentacles", numeral: "5", suit: "pentacles", meaning: "Scarcity, hardship, and the question of who is outside in the cold. The Five of Pentacles speaks to material struggle, to feeling left out or lacking. But look: the light from the window is there. Help is closer than it feels. Ask for what you need. Lean on the people who would genuinely show up.", keywords: ["hardship", "isolation", "financial struggle", "hope"], luckyColor: { name: "Gray", hex: "#8C8C8C" }, luckyNumber: 5, emoji: "❄️" },
  { name: "Six of Pentacles", numeral: "6", suit: "pentacles", meaning: "Generosity flows in both directions. The Six of Pentacles asks you to examine the balance of giving and receiving in your life. Are you sharing what you have with genuine generosity? Are you allowing yourself to receive what others offer? True abundance is in the circulation, not the accumulation.", keywords: ["generosity", "charity", "sharing", "receiving"], luckyColor: { name: "Yellow", hex: "#FFD93D" }, luckyNumber: 6, emoji: "🤲" },
  { name: "Seven of Pentacles", numeral: "7", suit: "pentacles", meaning: "Pause. Look at what you've grown. The Seven of Pentacles is the farmer leaning on the hoe, surveying the crop that isn't ready yet — but is coming. This card asks you to assess your progress with honesty and patience. You're further along than your impatience tells you. The harvest is coming.", keywords: ["patience", "investment", "progress", "assessment"], luckyColor: { name: "Mint", hex: "#55E6C1" }, luckyNumber: 7, emoji: "🌾" },
  { name: "Eight of Pentacles", numeral: "8", suit: "pentacles", meaning: "Diligence, mastery through practice, and the satisfaction of doing good work. The Eight of Pentacles is the craftsperson who shows up every day, who cares about quality, who is becoming more skilled through repetition. This is not glamorous work — it is the real work. Honor what you are becoming through your commitment.", keywords: ["diligence", "craftsmanship", "skill-building", "dedication"], luckyColor: { name: "Amber", hex: "#F5A623" }, luckyNumber: 8, emoji: "🔨" },
  { name: "Nine of Pentacles", numeral: "9", suit: "pentacles", meaning: "Elegant independence, earned comfort, and the pleasure of your own company. The Nine of Pentacles celebrates self-sufficiency — not isolation, but the deep satisfaction of having built something you can stand in. You have worked for this. You have earned this. Let yourself enjoy what you've created.", keywords: ["independence", "self-sufficiency", "abundance", "refinement"], luckyColor: { name: "Yellow", hex: "#FFD93D" }, luckyNumber: 9, emoji: "🌺" },
  { name: "Ten of Pentacles", numeral: "10", suit: "pentacles", meaning: "Legacy, lasting abundance, and the wealth that passes through generations. The Ten of Pentacles asks: what are you building that will outlast you? What does real security look like — for you, for those you love? This is not just about money. It's about the lasting meaning you are creating in the world.", keywords: ["legacy", "wealth", "family", "lasting security"], luckyColor: { name: "Yellow", hex: "#FFD93D" }, luckyNumber: 10, emoji: "🏛️" },
  { name: "Page of Pentacles", numeral: "Page", suit: "pentacles", meaning: "A student of the material world. The Page of Pentacles brings a grounded, practical curiosity — the desire to learn how things actually work, to develop real skills, to build something tangible. You're in an apprenticeship phase, and that's exactly where you need to be. Study. Experiment. Take it seriously.", keywords: ["ambition", "study", "learning", "opportunity"], luckyColor: { name: "Mint", hex: "#55E6C1" }, luckyNumber: 5, emoji: "📚" },
  { name: "Knight of Pentacles", numeral: "Knight", suit: "pentacles", meaning: "Slow and methodical — but absolutely certain to arrive. The Knight of Pentacles is not flashy. He is reliable, thorough, and committed to doing things right rather than fast. If this energy is available to you now, use it. The consistent, unglamorous effort is what actually builds something lasting.", keywords: ["reliability", "hard work", "thoroughness", "commitment"], luckyColor: { name: "Amber", hex: "#F5A623" }, luckyNumber: 14, emoji: "🏇🌿" },
  { name: "Queen of Pentacles", numeral: "Queen", suit: "pentacles", meaning: "Nourishment, practicality, and grounded abundance. The Queen of Pentacles tends to her domain with warmth and wisdom — creating environments where people thrive, managing resources with generosity, knowing exactly how to make something flourish. She is capable and caring. Let her approach inspire yours.", keywords: ["nurturing", "practicality", "abundance", "resourcefulness"], luckyColor: { name: "Mint", hex: "#55E6C1" }, luckyNumber: 3, emoji: "👸🌿" },
  { name: "King of Pentacles", numeral: "King", suit: "pentacles", meaning: "Mastery in the material world. The King of Pentacles has built something real, managed it wisely, and knows how to sustain what he's created. He is generous with his success because he understands that true wealth multiplies when shared. Lead with this kind of groundedness. Build things that last.", keywords: ["abundance", "security", "leadership", "generosity"], luckyColor: { name: "Yellow", hex: "#FFD93D" }, luckyNumber: 4, emoji: "👑🌿" }
];

// Pick today's card — deterministic, rotates through all 78
function getTodaysCard() {
  const now = new Date();
  const start = new Date(now.getFullYear(), 0, 0);
  const dayOfYear = Math.floor((now - start) / 86400000);
  return TAROT_CARDS[dayOfYear % TAROT_CARDS.length];
}

// Suit emoji prefix
function getSuitEmoji(suit) {
  const map = { major: '✨', wands: '🪄', cups: '🏆', swords: '⚔️', pentacles: '🪙' };
  return map[suit] || '✨';
}
```

**Rendering the card:**

```javascript
const card = getTodaysCard();
const suitDisplay = card.suit === 'major'
  ? `MAJOR ARCANA — ${card.numeral}`
  : `${card.suit.toUpperCase()} — ${card.numeral.toUpperCase()}`;
```

HTML structure for the tarot section:
```html
<div class="tarot-card">
  <div class="tarot-inner">
    <div class="tarot-header">YOUR CARD</div>
    <div class="tarot-title">[name]</div>
    <div style="font-size:72px;line-height:1;margin-bottom:12px;">[suitEmoji][cardEmoji]</div>
    <div class="tarot-numeral">[suitDisplay]</div>
    <div class="tarot-keywords">
      [keywords as .tarot-keyword spans]
    </div>
    <div class="tarot-meaning">"[meaning]"</div>
    <div class="tarot-footer">
      <span>Lucky #: [luckyNumber]</span>
      <span>Lucky Color: <div class="color-dot" style="background:[hex]"></div>[name]</span>
    </div>
  </div>
</div>
```

---

## Step 6 — Shared HTML Features (Both Tracks)

Both dashboards share the same JavaScript logic. The only differences are CSS class names and styling.

### Three Page Tabs

```html
<div class="page-tabs">
  <button class="page-tab active" onclick="showTab('dashboard',this)">DASHBOARD</button>
  <button class="page-tab" onclick="showTab('completed',this)">COMPLETED <span class="tab-badge" id="logCount">0</span></button>
  <button class="page-tab" onclick="showTab('history',this)">HISTORY</button>
</div>
```

- **Dashboard** — all live content
- **Completed** — Completed Log (first) then Daily Summary (second). VIEW & EDIT HISTORY button switches to History tab via `document.querySelectorAll('.page-tab')[2].click()` — NOT an external file link.
- **History** — `contenteditable="true"` day-entry blocks. Newest first. **Never overwrite by scheduled refresh.**

### Persistent State (localStorage)

All state is stored in `localStorage` under the key `comms-dashboard-state` (or a user-prefixed variant if multiple users share a machine):

```javascript
function lsGet() { try { return JSON.parse(localStorage.getItem('comms-dashboard-state')||'{}'); } catch(e) { return {}; } }
function lsSet(obj) { localStorage.setItem('comms-dashboard-state', JSON.stringify(obj)); }
```

State keys:
- `completed` — object mapping item titles to timestamps; items are hidden on restore
- `log` — array of completed log entries `{title, ts, source, priority}`
- `customTasks` — array of user-added tasks `{title, priority}`
- `dismissed` — object mapping draft IDs to timestamps

All state persists **indefinitely** — no expiry.

### IIFE: restoreState()

Runs on page load. Re-hides completed items, rebuilds completed log, re-inserts custom tasks, re-hides dismissed drafts, calls `updateKPIs()`.

### Live KPI Updates

```javascript
function updateKPIs() {
  const all = document.querySelectorAll('.action-item:not(.done)');
  const high = document.querySelectorAll('.action-item[data-priority="high"]:not(.done)');
  if (document.getElementById('kpiTotal')) document.getElementById('kpiTotal').textContent = all.length;
  if (document.getElementById('kpiHigh')) document.getElementById('kpiHigh').textContent = high.length;
}
```

Add `id="kpiTotal"` to the total action items KPI value and `id="kpiHigh"` to the high-priority KPI value.

### Filter Buttons

```javascript
function filterItems(filter) {
  document.querySelectorAll('.filter-btn').forEach(b => b.classList.remove('active'));
  event.currentTarget.classList.add('active');
  document.querySelectorAll('.action-item').forEach(item => {
    if (item.classList.contains('done')) { item.style.display = 'none'; return; }
    const show = filter === 'all' || item.dataset.priority === filter || item.dataset.source === filter;
    item.style.display = show ? 'flex' : 'none';
  });
}
```

### Add Custom Task

Yellow "+ ADD TASK" button in the filter bar. Prompts for title and priority, inserts into DOM in the right priority section, saves to localStorage.

### Auto-Complete Resolved Items

```html
<script id="auto-resolved" type="application/json">[]</script>
```

An `autoComplete()` IIFE reads this array on page load and auto-completes matching action items (items from the previous refresh that are now resolved: question answered, deliverable submitted, event passed). The scheduled refresh task populates this array. Title must exactly match `.item-title` textContent.

### Charts

Chart.js CDN: `https://cdn.jsdelivr.net/npm/chart.js@4.5.1`

Two doughnut charts: Priority breakdown (High/Medium/Low) and Source breakdown (Slack/Email/Docs). Use the track's color palette. Add `borderWidth: 3, borderColor: '#1A1A2E'` for the Creative track.

### Daily Summary (Completed Tab)

Three paragraphs: **Wins**, **New Connections & Meetings**, **What I Got Done**. No bullet points. No confidential information. Include job titles for senior leaders when relevant.

---

## Step 7 — Save the Dashboard

Save the HTML file to the user's workspace folder. Suggested names:
- `[name]-dashboard.html` (e.g., `jordan-dashboard.html`)
- Or a neutral `communications-dashboard.html`

Create a subfolder if the workspace allows.

---

## Step 8 — Create a Live-Reload Server Script (Optional)

Create a `Start Dashboard.command` file in the same folder. This is a macOS double-clickable script that starts a live-reload server via `npx live-server` so the browser auto-refreshes when the scheduled task updates the HTML.

```bash
#!/bin/bash
PORT=8042
DIR="$(cd "$(dirname "$0")" && pwd)"
DASHBOARD_FILE="YOUR-DASHBOARD.html"
if ! command -v npx &> /dev/null; then
  echo "Error: Node.js is required. Install from https://nodejs.org"; exit 1
fi
echo "◆ Dashboard running at http://localhost:$PORT"
cd "$DIR"
npx -y live-server --port=$PORT --open=$DASHBOARD_FILE --watch=$DASHBOARD_FILE --no-browser &
sleep 2
open "http://localhost:$PORT/$DASHBOARD_FILE"
wait
```

Make executable: `chmod +x "Start Dashboard.command"`. Requires Node.js.

---

## Step 9 — Set Up Auto-Refresh Schedule

Create a scheduled task that refreshes the dashboard every hour during work hours.

**CRITICAL — Incremental Refresh:** Use the **Edit tool** (targeted find-and-replace) — never Write/rewrite the full file. This preserves user edits in the History tab and completed state.

Scheduled task instructions:
1. Read the existing dashboard HTML file
2. Pull fresh data from Slack, Outlook, and Google Docs (last 2 hours)
3. Use Edit tool to update ONLY: KPI values, action items, draft replies, docs list, daily summary, auto-resolved JSON array
4. For Creative track: also rotate the tarot card — embed the `TAROT_CARDS` array and `getTodaysCard()` function to pick today's card deterministically from the full 78-card deck
5. NEVER touch: `<style>` block, `<script>` block, tab structure, History tab content, Completed Log order

Use `create_scheduled_task` with:
- `taskId`: `refresh-comms-dashboard` (or personalized)
- `cronExpression`: `0 8-17 * * 1-5`

Remind the user to click "Run now" once to pre-approve Slack, Outlook, and Google Drive tool permissions.

---

## Step 10 — Present to the User

Share the dashboard file link and tell them:
- Style selected and what's in it
- How many action items were found and their priority breakdown
- That the hourly refresh is set up (remind them to click Run Now to approve permissions)
- That drafts have been pushed to Slack and are ready to send

---

## Example Prompts That Trigger This Skill

- "Build me a communications dashboard"
- "What do I need to respond to across Slack and email?"
- "Show me my action items from today"
- "I want a clean professional dashboard of my messages"
- "Make me a colorful fun dashboard with a tarot card"
- "What's on my plate today?"
- "Communications overview"
- "Activity dashboard"
- "Whimsical dashboard"
- "Memphis style dashboard"
