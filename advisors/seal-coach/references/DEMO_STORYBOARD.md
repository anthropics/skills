# SEAL Security Coach — Demo Video Storyboard

Synthesis Hackathon submission demo. Target: 2:30 - 3:00.

## Format

Remotion project. Terminal-style UI with typing animations, coach response overlays,
and caption callouts. No voiceover — text captions tell the story.

## Visual Style

- Dark terminal background (#1a1b26 or similar)
- Monospace font (JetBrains Mono or Fira Code)
- Coach responses in a bordered panel (green accent for "good" actions, red/amber for warnings)
- Caption text: white on semi-transparent dark overlay at bottom
- Typing animation: character-by-character with blinking cursor
- Cursor: blinking block or thin bar

## Color Palette

| Element | Color | Hex |
|---------|-------|-----|
| Background | Dark blue-black | #1a1b26 |
| User text | White | #c0caf5 |
| Coach text | Green | #9ece6a |
| Warnings/Gaps | Amber | #e0af68 |
| Accent/Actions | Blue | #7aa2f7 |
| Critical band | Red | #f7768e |
| Developing band | Amber | #e0af68 |
| Established band | Blue | #7aa2f7 |
| Advanced band | Green | #9ece6a |
| Caption overlay | White on 80% black | — |

---

## Scene 1: Hook (0:00 - 0:15)

### Visual
- Screen fades in from black to empty terminal
- Cursor blinks 2-3 times
- Text types in: `I think we might get hacked`
- Text fades, replaced by title card

### Title Card
```
SEAL Security Coach
27 domains. 213 controls. One conversation.

Synthesis Hackathon
```

### Caption
"Open source projects can't afford security consultants."

### Timing
- 0:00-0:03: Fade in, cursor blink
- 0:03-0:06: Type user message
- 0:06-0:15: Title card with fade

---

## Scene 2: Urgency Flow (0:15 - 1:00)

### Visual
- Terminal splits: user input on left, coach response panel on right
- Coach response appears with typing effect (faster than user typing)

### Exchange 1 (0:15 - 0:30)

**User types:**
```
I think we might get hacked
```

**Coach panel slides in from right:**
```
┌─ 🔒 Security Coach ──────────────────────┐
│                                            │
│ Let's figure out where the risk is.        │
│ Are you more worried about                 │
│ wallet/key compromise, or someone          │
│ getting into your infrastructure?          │
│                                            │
└────────────────────────────────────────────┘
```

### Exchange 2 (0:30 - 0:45)

**User types:**
```
Wallet. We have a multisig treasury but
I'm not sure we're doing enough.
```

**Coach panel updates:**
```
┌─ 🔒 Security Coach ──────────────────────┐
│                                            │
│ Quick question: if one signer's device     │
│ was compromised right now, could the       │
│ attacker drain funds?                      │
│                                            │
└────────────────────────────────────────────┘
```

### Exchange 3 (0:45 - 1:00)

**User types:**
```
We use 2-of-3 multisig. But two of us
have our keys on the same laptop.
```

**Coach panel with amber warning border:**
```
┌─ ⚠️ Security Coach ─────────────────────┐
│                                            │
│ That's the gap. If that laptop is          │
│ compromised, an attacker has 2 of 3       │
│ keys — game over.                          │
│                                            │
│ Three things you can do RIGHT NOW:         │
│                                            │
│ 1. Split keys — use a hardware wallet      │
│ 2. Set a timelock for large transfers      │
│ 3. Verify signers stored keys safely       │
│                                            │
└────────────────────────────────────────────┘
```

### Caption
"Context-specific. Actionable. Immediate."

---

## Scene 3: Readiness Bands (1:00 - 1:30)

### Visual
- Terminal shows readiness summary appearing line by line
- Color-coded progress bars animate in

### Summary appearing:

```
Security Readiness:

wallet-security:      [████████░░] Developing
incident-management:  [███░░░░░░░] Critical
iam:                  [██████████] Established
devsecops:            [█████░░░░░] Developing
governance:           [██░░░░░░░░] Critical
```

### Bars animate:
- Critical fills red to 30%
- Developing fills amber to 50-60%
- Established fills blue to 100%
- Each bar fills with a smooth interpolation (ease-out)

### Caption
"Not pass/fail. Readiness bands that show where you are and where to go."

---

## Scene 4: Hardening Plan (1:30 - 1:55)

### Visual
- Coach panel shows phased plan
- Each phase fades in with a slight delay (sequencing)
- Action items appear with checkmark icons

### Panel content (phases appear sequentially):

```
┌─ 🛡️ Hardening Plan ─────────────────────┐
│                                            │
│ Phase 1: Quick Wins (Week 1-2)             │
│   ☐ Split multisig keys across HW wallets  │
│   ☐ Enable MFA on all admin accounts       │
│   ☐ Save SEAL 911 emergency contact        │
│                                            │
│ Phase 2: Foundation (Week 3-6)             │
│   ☐ Write incident response playbook       │
│   ☐ Add semgrep to CI/CD pipeline          │
│   ☐ Set up transaction monitoring          │
│                                            │
│ Phase 3: Strengthen (Week 7-12)            │
│   ☐ Formal threat model                    │
│   ☐ Tabletop incident exercises            │
│   ☐ Automated compliance checks            │
│                                            │
└────────────────────────────────────────────┘
```

### Caption
"Every action maps to specific SEAL framework controls. No vague advice."

---

## Scene 5: Onboarding (1:55 - 2:15)

### Visual
- Coach panel shows check-in offer
- User types response
- Quick confirmation animation

### Coach panel:
```
┌─ 🔒 Security Coach ──────────────────────┐
│                                            │
│ I can set up check-ins so this isn't       │
│ a one-time thing:                          │
│                                            │
│ 1. Daily security tip                      │
│ 2. Weekly progress check-in                │
│ 3. Team accountability pings               │
│                                            │
│ I won't set anything up until you confirm. │
│                                            │
└────────────────────────────────────────────┘
```

**User types:**
```
Yeah, daily tip + weekly check-in
```

**Confirmation flash:**
```
✓ Daily tip scheduled (9am)
✓ Weekly check-in scheduled (Monday 10am)
```

### Caption
"Coach asks. You confirm. Then it sets up. No silent automations."

---

## Scene 6: Return Visit (2:15 - 2:35)

### Visual
- Screen transitions (slide or fade) to a new session
- Fresh terminal, new timestamp
- Coach remembers

### Screen refreshes, new session:

**User types:**
```
How's my security posture?
```

**Coach panel:**
```
┌─ 🔒 Security Coach ──────────────────────┐
│                                            │
│ Last time we identified                    │
│ incident-management as Critical.           │
│                                            │
│ Want to pick up there?                     │
│                                            │
└────────────────────────────────────────────┘
```

### Caption
"Memory across sessions. It picks up where you left off."

---

## Scene 7: Close (2:35 - 2:50)

### Visual
- All elements fade except background
- Title and tagline fade in
- Links appear

### Text (centered):

```
SEAL Security Coach

Open source security for everyone.

github.com/clanktank/seal-skills
Synthesis Hackathon

Built on SEAL Frameworks
27 domains · 213 controls
```

### Fade to black

---

## Technical Notes for Remotion Implementation

### Composition Structure
```
Root (30fps, 1080p, ~2:50 total)
├── Scene1_Hook (0:00-0:15) — 15s
├── Scene2_Urgency (0:15-1:00) — 45s
├── Scene3_Readiness (1:00-1:30) — 30s
├── Scene4_Plan (1:30-1:55) — 25s
├── Scene5_Onboarding (1:55-2:15) — 20s
├── Scene6_Return (2:15-2:35) — 20s
└── Scene7_Close (2:35-2:50) — 15s
```

### Key Animations
- **Typing**: use `interpolate` with `inputRange` per character count
- **Panel slide-in**: `spring()` with stiffness=200
- **Progress bars**: `interpolate(frame, [start, end], [0, percentage])`
- **Phase reveal**: staggered `Sequence` components with 0.3s delay
- **Color transitions**: `interpolateColors()` for band colors
- **Cursor blink**: `useCurrentFrame() % 30 < 15` toggle

### Assets Needed
- Terminal background texture (subtle grain, optional)
- JetBrains Mono font (or system monospace)
- Sound effect for typing (optional, keyboard clicks)
- Transition sound for scene changes (optional)

### Captions
- Use `display-captions` rules for word-highlighting style
- Or simple bottom-overlay text with fade timing
- Font: sans-serif, slightly smaller than terminal text
- Semi-transparent dark background behind text
