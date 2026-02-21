# Episode Template

## Standard Episode Structure

---

### [COLD OPEN — NEWS DESK]

**The Anchor** delivers the sanitized official version of the event.

- Tone: Authoritative. Bland. Completely inadequate.
- Duration: 30–45 seconds
- Animation style: South Park flat
- Setting: Anchor desk, full studio environment

**Script format:**

> "Tonight — [EVENT IN ONE CLAUSE]. [SECOND CLAUSE THAT DOESN'T EXPLAIN THE FIRST ONE]. We have a closer look."

The cold open establishes the official version. The entire rest of the episode is about how that version fails.

---

### [TITLE CARD]

> **"What actually happened — according to [CHARACTER NAME]"**

- Full-screen card
- Character's name in the title should be their archetype label, not a personal name
- Brief pause before cut

---

### [CHARACTER POV SEQUENCE]

The same event, filtered through the character's worldview.

Reality is distorted in the specific direction of their archetype. The distortion is internally consistent — the character is not lying, they are perceiving.

**Style:** Character's assigned animation mode (flat or fluid).

---

#### POV Sequence Structure

**Beat 1 — Establishing shot (character in their environment)**

The character's home context. This is where they receive the news, or where the event touches their world. The environment should communicate the archetype before the character speaks.

| Character | Home Environment |
|---|---|
| The MAGA Cultist | Living room, TV, phone in hand |
| The Typical Leftist | Coffee shop, laptop open, tote bag on chair |
| The Informed Person | Home or library — book or paper nearby |
| The Opportunist | Office or conference room — always mid-meeting-adjacent |
| The Talking Head | Studio — or a setting that reads as studio |

---

**Beat 2 — The event, filtered**

The same event the Anchor just described — but now through this character's perceptual system.

Apply the character's POV distortion rules (documented in their character file under **POV Distortion Rules**):

| Character | POV Distortion Direction |
|---|---|
| The MAGA Cultist | He is the hero; contradiction becomes conspiracy evidence |
| The Typical Leftist | She is the most aware; her contradictions are invisible |
| The Informed Person | No distortion — which is the most unsettling version |
| The Opportunist | He is the moderate adult; benefit calculation runs visibly |
| The Talking Head | Everything is unprecedented; facts appear and vanish |

---

**Beat 3 — The signature prop moment**

Each character has a signature prop that appears in a key-action moment during the POV sequence.

| Character | Prop | Moment |
|---|---|---|
| The MAGA Cultist | Phone, mid-scroll | Finds confirmation — the scroll stops, the share happens |
| The Typical Leftist | Reusable cup + phone | Posts about the cause while holding the irony |
| The Informed Person | Book, set down | The moment he stops being able to not engage |
| The Opportunist | Business card + head tilt | The calculation completes — the card appears |
| The Talking Head | Tablet glance | The glance-and-away — the gesture of information without transfer |

---

**Beat 4 — Climax of distortion**

The moment where the character's worldview reaches its most extreme expression in relation to the event.

This is the comedic or dramatic peak. It should be the most concentrated expression of the archetype — the thing that would make someone watching say: *yes, that is exactly what that person would do.*

---

**Beat 5 — Return signal**

A brief moment that signals the POV sequence is ending. The character's expression or action returns them to their stable state — because nothing that just happened will change them.

| Character | Return State |
|---|---|
| The MAGA Cultist | Returns to scroll — already looking for the next confirmation |
| The Typical Leftist | Returns to mild indignation — the crisis absorbed, filed, and accessorized |
| The Informed Person | Picks the book back up (or tries to) |
| The Opportunist | Business card goes back, phone comes out — position still tracking |
| The Talking Head | New crisis already beginning — this one is already over |

---

### [BUTTON]

Brief return to news desk. **The Anchor** moves on without acknowledgment.

> **"In other news..."**

- Duration: 5–10 seconds
- The Anchor's expression: identical to the cold open. Unchanged.
- The transition from POV content to "In other news" is the punchline.
- Do not editorialize. Do not linger. Do not let The Anchor acknowledge what just happened.

---

## Multi-Character Episodes

In episodes featuring multiple POV sequences:

- Each POV sequence follows the 5-beat structure above
- The Anchor returns between each POV with a brief transition line
- The same event is rendered 2–4 times through different archetypes
- The Informed Person's POV, if included, should be last — the undistorted version lands differently after several distorted ones

**Transition between POV sequences:**

> **"For another perspective..."**

Brief Anchor moment — same desk, same expression, identical intonation to the cold open.

---

## Global Guest Character Episodes

When a global character appears:

1. The Anchor introduces them with a geographic/political identifier — no personal name
2. The guest character receives their own title card variant:
   > **"What actually happened — according to [ARCHETYPE], [LOCATION/CONTEXT]"**
3. The guest's POV follows the same 5-beat structure
4. Animation style is determined by narrative role (see `README.md` → Global Guest Characters)
5. The button returns to The Anchor — same transition, same non-acknowledgment

---

## Running Time Guidelines

| Segment | Duration |
|---|---|
| Cold open (Anchor) | 30–45 sec |
| Title card | 3–5 sec |
| POV sequence (single character) | 90–180 sec |
| Button | 5–10 sec |
| **Single-character episode total** | ~3–4 min |
| **Multi-character episode (3 POVs)** | ~8–10 min |

---

## Visual Continuity Notes

- The Anchor desk environment is **identical in every episode** — same colors, same framing, same papers
- The POV environment changes per character but is consistent within a character's appearances
- The cut between Anchor and POV should feel like a channel change — a visual register shift
- The cut back from POV to Anchor should feel like a reset — the POV didn't happen, officially

---

## What This Template Is Not

This template does not include:
- Specific dialogue (episode-specific)
- B-roll or cutaway descriptions (episode-specific)
- Character voice direction (see individual character files)
- Specific event content (news-cycle dependent)

For episode-specific breakdowns, create a new file in `storyboard/` following the naming convention: `ep-[number]-[slug].md`
