# Color Palette — The Talking Head

**Animation style:** South Park flat cutout
**Character archetype:** Corporate media amplifier — everything is a crisis, nothing is explained

---

## Palette

| Element | Name | Hex | RGB | Usage |
|---|---|---|---|---|
| Primary | Network red | `#CC2222` | 204, 34, 34 | Power garment — dominant suit or equivalent |
| Secondary | Corporate navy | `#1A2A5E` | 26, 42, 94 | Alternate suit — rotates with primary |
| Tertiary | Broadcast gold | `#C8A830` | 200, 168, 48 | Accent — tie, brooch, button detail |
| Skin | Overlit warm | `#D4A882` | 212, 168, 130 | Skin base — overlit from years of studio lighting |
| Accent | White hot | `#FFFFFF` | 255, 255, 255 | Collar, teeth, peak broadcast luminosity |

---

## Extended Palette

| Element | Hex | Notes |
|---|---|---|
| Suit shadow (red) | `#961A1A` | Shadow pass on network red suit |
| Suit shadow (navy) | `#0E1A3E` | Shadow pass on corporate navy suit |
| Gold shadow | `#9A7C20` | Shadow pass on broadcast gold accent |
| Skin shadow | `#A87850` | Single shadow stop — overlit, so shadow is limited |
| Skin highlight | `#E8C8A0` | Overlit — highlight is pronounced |
| Outline | `#1A1A1A` | Standard South Park black |
| Makeup highlight | `#EED0B0` | Slightly brighter than skin — makeup layer |
| Hair | `#1A1A1A` + solid fill | Perfect, single-shape, does not move |
| Tablet | `#222222` | Device body |
| Tablet screen | `#2A3A6A` | Screen on — implies content, delivers nothing |
| Teeth | `#FFFFFF` | White hot — the smile is a broadcast element |

---

## Hair Design Note

The hair is a single solid shape. In South Park flat, it does not move, separate, or vary between shots. It is correct in every orientation, which is only possible if it is not real hair — it is a hair-adjacent structure.

| Element | Hex | Notes |
|---|---|---|
| Hair body | `#1A1A1A` | Single fill — no sheen, no variation |
| Hair shape | Solid geometric | No individual strands implied |

**Hair note:** In a sense, the hair being `#1A1A1A` — the same as the outline — is appropriate. There is no boundary between the person and the performance at the level of the hair. It is part of the character's outline.

---

## Skin: "Overlit Warm"

The skin tone `#D4A882` is described as "overlit warm" — the specific quality of someone who has spent a disproportionate percentage of their life under studio lighting. It is warmer and slightly more saturated than natural skin at this tone would appear in standard light.

| Element | Hex | Notes |
|---|---|---|
| Skin base | `#D4A882` | Overlit — warmer than natural |
| Skin shadow | `#A87850` | Shadow limited — overlit environments suppress shadow |
| Skin highlight | `#E8C8A0` | Pronounced — the studio lighting is aggressive |
| Makeup layer | `#EED0B0` | Slightly lighter, applied — visible in South Park flat as a slightly different value |

**South Park flat note:** The makeup being visible at the geometry level — a slightly brighter fill on the face area — communicates the studio-prepared quality without requiring a separate pass.

---

## Network Color Variants

The Talking Head wears a different network color in different episodes, cycling through:

| Variant | Primary | Accent |
|---|---|---|
| Network red (default) | `#CC2222` | `#C8A830` gold |
| Corporate navy | `#1A2A5E` | `#CC2222` red accent |
| Broadcast gold | `#C8A830` | `#1A2A5E` navy accent |

**The broadcast gold variant** is reserved for high-stakes episodes — it reads as more expensive, which communicates more urgency.

---

## Tablet Prop

| Element | Hex | Notes |
|---|---|---|
| Device body | `#222222` | Dark, thin — current |
| Screen active | `#2A3A6A` | Navy-tinted — implies graphics, content |
| Screen glance indicator | `#4A6AAA` | Slightly lighter — the screen is being looked at (not read) |

**Prop note:** The tablet glance-and-away animation is one of the most important recurring beats. The screen color suggests information. The glance duration is insufficient for information to transfer. These two things together are the prop's entire function.

---

## Palette Design Intent

The Talking Head's palette is the palette of broadcast television — the specific palette designed to communicate importance through color before any content is delivered. Network red is the color of urgency. Corporate navy is the color of authority. Broadcast gold is the color of premium tier.

**The white hot accent** (`#FFFFFF`) appears at the collar and the teeth — the two most luminous points in a broadcast close-up. Both are performance elements. The collar announces formality. The teeth announce delivery. Neither communicates content.

**The overlit skin** completes the broadcast signal: this person exists in studio light. They are a broadcast entity. They are appropriately lit for a screen. The fact that they appear in non-broadcast environments with the same lighting effect communicates that the performance never stops.

---

## Application Rules (South Park Flat)

- Flat fills only — no gradients
- Outline: `#1A1A1A` at 3px
- Hair: single solid shape — same fill as outline — does not move
- Eyebrow geometry: raised 3mm above standard position — this is a construction parameter, not an expression
- Makeup: skin fill is slightly lighter than standard skin tone — `#EED0B0` face area vs `#D4A882` neck/hands
- Tablet in hand in all shots — glance animation consistent and insufficient
- Teeth visible when mouth is open — `#FFFFFF` white hot
