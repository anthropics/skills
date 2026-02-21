# Character Board — Political Satire Animation Project

## Premise

A viewer watches the news. Each episode cuts to an "inside look" at what actually happened, told from a specific character's distorted point of view.

The Anchor delivers the sanitized official version. Then we cut inside — same event, five different realities, each one shaped entirely by the character's archetype.

---

## Style

US-centered political satire. Core cast of 5 recurring archetypes. Global characters appear as episode-specific guests.

Two animation modes:

| Mode | Used For |
|---|---|
| South Park flat cutout | Characters with rigid, symbolic worldviews |
| Boondocks anime-fluid | Characters with emotional complexity or physical expressiveness |

---

## Core Cast

| Character | File | Animation Style |
|---|---|---|
| The Anchor *(frame)* | `frame/the-anchor.md` | South Park flat |
| The MAGA Cultist | `core-cast/maga-cultist.md` | South Park flat |
| The Typical Leftist | `core-cast/typical-leftist.md` | South Park flat |
| The Informed Person | `core-cast/informed-person.md` | Boondocks fluid |
| The Opportunist | `core-cast/opportunist.md` | Boondocks fluid |
| The Talking Head | `core-cast/talking-head.md` | South Park flat |

---

## Style Assignment Rationale

| Character | Style | Reason |
|---|---|---|
| The Anchor | Flat | Symbolic, institutional, no inner life |
| The MAGA Cultist | Flat | Rigid worldview — symbolic not expressive |
| The Typical Leftist | Flat | Performative — the flatness mirrors the performance |
| The Informed Person | Fluid | Emotional complexity, internal life visible |
| The Opportunist | Fluid | Calculation requires readable microexpressions |
| The Talking Head | Flat | Pure surface — flat is the point |

---

## Directory Structure

```
character-board/
├── README.md                          ← this file
├── frame/
│   └── the-anchor.md                  ← frame character / viewer entry point
├── core-cast/
│   ├── maga-cultist.md
│   ├── typical-leftist.md
│   ├── informed-person.md
│   ├── opportunist.md
│   └── talking-head.md
├── assets/
│   ├── color-palettes/                ← per-character color data
│   │   ├── the-anchor.md
│   │   ├── maga-cultist.md
│   │   ├── typical-leftist.md
│   │   ├── informed-person.md
│   │   ├── opportunist.md
│   │   └── talking-head.md
│   └── svg-maps/
│       └── README.md                  ← SVG asset map index (populated per episode)
└── storyboard/
    └── episode-template.md            ← standard episode structure
```

---

## Global Guest Characters

Global characters appear in specific episodes only. Introduced through The Anchor's desk before their POV cut. Animation style assigned per episode based on narrative role — flat if serving a symbolic function, fluid if carrying dramatic weight.

Placeholder archetypes for future episodes:

| Archetype | Style |
|---|---|
| The Nationalist Strongman | Boondocks fluid |
| The Technocrat | South Park flat |
| The Revolutionary | Boondocks fluid |
| The Multilateral Bureaucrat | South Park flat |

---

## Episode Format

See `storyboard/episode-template.md`.

---

*Version 1.0 — Character Board*
*Branch: feature/character-board*
*Next: Storyboard template → feature/storyboard branch*
