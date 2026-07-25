# Asset Pipeline Reference

Every image asset must be inspected and judged before use in any 2.5D site.
The AI inspects, judges, and informs — it does NOT auto-remove backgrounds.

---

## Step 1 — Run the Inspection Script

Run `scripts/inspect-assets.py` on every uploaded image before doing anything else.
The script outputs the format, mode, size, background type, and a recommendation
for each image. Read its output carefully.

---

## Step 2 — Judge Whether Background Removal Is Actually Needed

The script detects whether a background exists. YOU must decide whether it matters.

### Remove the background if the image is:
- An isolated product on a studio backdrop (bottle, shoe, phone, fruit, object)
- A character or figure that needs to float in the scene
- A logo or icon placed at any depth layer
- Any element at depth-2 or depth-3 that needs to "float" over other content
- An asset where the background colour will visibly clash with the site background

### Keep the background if the image is:
- A screenshot of a website, app UI, dashboard, or software
- A photograph used as a section background or depth-0 fill
- An artwork, poster, or illustration that is viewed as a complete piece
- A device mockup or "image inside a card/frame" design element
- A photo where the background is part of the visual content
- Any image placed at depth-0 — it IS the background, keep it

### When unsure — ask the role:
> "Does this image need to float freely over other content?"
> Yes → remove bg. No → keep it.

---

## Step 3 — Resize to Depth-Appropriate Dimensions

Run the resize step in `scripts/inspect-assets.py` or do it manually.
Never embed a large image when a smaller one is sufficient.

| Depth | Role | Max Longest Edge |
|---|---|---|
| 0 | Background fill | 1920px |
| 1 | Glow / atmosphere | 800px |
| 2 | Mid decorations, companions | 400px |
| 3 | Hero product | 1200px |
| 4 | UI components | 600px |
| 5 | Particles, sparkles | 128px |

---

## Step 4 — Inform the User (Required for Every Asset)

Before outputting any HTML, always show an asset audit to the user.

For each image that has a background issue, use this exact format:

> ⚠️ **Asset Notice — [filename]**
>
> This is a [JPEG / PNG] with a solid [black / white / coloured] background.
> As-is, it will appear as a visible box on the page rather than a floating asset.
>
> Based on its intended role ([product shot / decoration / etc.]), I think the
> background [should be removed / should be kept because it's a [screenshot/artwork/bg fill/etc.]].
>
> **Options:**
> 1. Provide a new PNG with a transparent background — best quality, ideal
> 2. Proceed as-is with a CSS workaround (mix-blend-mode) — quick but approximate
> 3. Keep the background — if this image is meant to be seen with its background
>
> Which do you prefer?

For clean images, confirm them briefly:

> ✅ **[filename]** — clean transparent PNG, resized to [X]px, assigned depth-[N] ([role])

Show all of this BEFORE outputting HTML. Wait for the user's response on any ⚠️ items.

---

## Step 5 — CSS Workaround (Only After User Approves)

Apply ONLY if the user explicitly chooses option 2 above:

```css
/* Dark background image on a dark site — black pixels become invisible */
.on-dark-bg {
  mix-blend-mode: screen;
}

/* Light background image on a light site — white pixels become invisible */
.on-light-bg {
  mix-blend-mode: multiply;
}
```

Always add a comment in the HTML when using this:
```html
<!-- CSS approximation: [filename] has a solid background.
     Replace with a transparent PNG for best quality. -->
```

Limitations:
- `screen` lightens mid-tones — only works well on very dark site backgrounds
- `multiply` darkens mid-tones — only works well on very light site backgrounds
- Neither works on complex or gradient backgrounds
- A proper cutout PNG always gives better results

---

## Step 6 — CSS Rules for Transparent Images

Whether the image came in clean or had its background resolved, always apply:

```css
/* ALWAYS use drop-shadow — it follows the actual pixel shape */
.product-img {
  filter: drop-shadow(0 30px 60px rgba(0, 0, 0, 0.4));
}

/* NEVER use box-shadow on cutout images — it creates a rectangle, not a shape shadow */

/* NEVER apply these to transparent/cutout images: */
/*
  border-radius           → clips transparency into a rounded box
  overflow: hidden        → same problem on the parent element
  object-fit: cover       → stretches image to fill a box, destroys the cutout
  background-color        → makes the bounding box visible
*/
```
