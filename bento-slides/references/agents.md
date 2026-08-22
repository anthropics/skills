# bento/slides — for AI agents

**Guide version `1.0.18`** · document format `bento/slides` (v1). This
guide matches the bento/slides shell of the same version. A deck's `#bento-doc`
JSON is always the source of truth — if it was written by a newer shell it may
carry features beyond this guide; unknown keys are ignored, never fatal.

> **Bento is a suite.** Slides is the first app; **Spaces**
> (`bento/spaces`, notes and wiki) ships alongside it. **Dash** (`bento/dash`,
> data and sheets) is in development, and a word processor is planned. Each ships
> as its own self-contained distributable — `Bento_Slides.bento.html`,
> `Bento_Spaces.bento.html`, and so on — with its own agent guide at
> `bento.page/<app>/agents.md`. **This guide covers Slides only.** Before you
> edit a file, check its `"format"` field and use the matching guide; if the
> format is one you have no guide for, don't guess at its shape.

*Drop this file into your context (or point your harness at it) and you can
author and edit Bento presentations directly. Also published at
[bento.page/agents.md](https://bento.page/agents.md). For **Claude Code**,
install the packaged **bento-slides** skill once and it triggers automatically
(or via `/bento-slides`) — it can even download the latest Bento app itself,
so a deck can be authored from an empty folder:*

```
/plugin marketplace add nyblnet/bento
/plugin install bento-slides@bento
```

*…or as a plain personal skill:*

```bash
mkdir -p ~/.claude/skills/bento-slides && curl -fsSL https://bento.page/skills/bento-slides/SKILL.md -o ~/.claude/skills/bento-slides/SKILL.md
```

*(claude.ai / Claude Desktop: upload
[bento.page/skills/bento-slides.zip](https://bento.page/skills/bento-slides.zip)
under Settings → Skills.)*

**Working without the skill, from an empty folder?** Download the app itself —
this is the file you write your document into:

```bash
curl -fsSL https://bento.page/releases/slides/Bento_Slides.bento.html -o "<Topic>.bento.html"
```

The downloaded file's `#bento-doc` block is **empty**. That is expected: opened
in a browser it mints a fresh showcase deck to get a new user started, but on
disk there is nothing to discard and nothing to copy from. Write your document
into the empty block.

A Bento deck (`*.bento.html`) is a self-contained HTML file. The document
lives in ONE plaintext block near the top:

```html
<script type="application/bento+json" id="bento-doc">
{ "format": "bento/slides", ... }
</script>
```

> ### Before you read a deck: it may carry its own keys
>
> If a deck has live collaboration switched on, its `#bento-doc` block contains
> the credentials to that session — the room key, and depending on the copy, a
> writer or owner private key. That is deliberate and it is what makes sharing
> work without accounts: **the file is the invitation**, so opening a copy joins
> the room.
>
> The consequence is easy to miss, because nothing about a document looks like a
> credential. Anything that receives the file receives the room: a chat, a
> ticket, a harness, a model provider's logs. Not because anything is broken —
> that is simply what the file is.
>
> **So, before you take a deck into your context:**
>
> 1. Look for a `"collab"` key in the document. No `collab`, or a `collab` with
>    no `ownerPriv` / `writerPriv` / `invite`, and there is nothing to leak.
> 2. If those are present, **say so before continuing.** The person may not know
>    their deck is live, and they are the only one who can decide.
> 3. Prefer a copy that carries no keys: *Save ▾ → Save read-only copy…* or
>    *Share → Stop sharing* on a duplicate. In the browser,
>    `window.bento.validate()` reports this as `collab-secrets-present`.
>
> Editing the JSON in place is fine and does not change any of this — the
> exposure is in *reading* the file, not writing it. And note that removing the
> keys after the fact does not retract them: if a shared deck has already gone
> somewhere, the remedy is *Share → Rotate keys*, which revokes the old room.

Two ways to work with it:

1. **File harness** (Claude Code, agent sandboxes): edit the JSON inside the
   `#bento-doc` block in place. Escape every `<` in the JSON as `\u003c`
   so the block can never contain a literal `</script>`. Leave everything else in the
   file untouched.
2. **Chat round-trip** (any chatbot): the user copies the JSON out via
   *Save → Copy document JSON*, you return a full replacement document,
   they paste it back via *Save → Replace from JSON…* (undoable).
   In the browser console: `window.bento.doc` (read) /
   `window.bento.loadDoc(json)` (write, undoable).

---

## Make a GREAT deck, not just a correct one

**Read this section first — it is the difference between a wall of text and a
Bento deck.** The format's whole value is motion, morph, charts and
interactivity. A correct-but-static result (bullets on slides) wastes it and
is the #1 failure mode. The move is to look at the *source material* and map
each kind of content to the feature built for it:

| When the material is… | Reach for | Why |
|---|---|---|
| numbers to **compare visually** (trend, magnitude, share) | a **chart** element | bars/lines read instantly |
| a **comparison / spec / pricing / feature grid** (rows × columns of labels + values) | a **table** element | structured cells beat 20 hand-placed text boxes; it styles cohesively |
| consecutive slides about the **same thing changing** (before/after, process steps, a metric across stages) | **morph**: same element `id` on both slides + `transition:"morph"` on the later one | the shared elements glide; this is Bento's signature and is *almost always missed* |
| a point to **drill into** (a definition, "click to see how", a sub-topic) | a **state slide** (`stateOf` + element `link`) | keeps the linear story clean; the detail is one click away |
| a **hero / full-slide image** | full-bleed image + scrim rect + text, with **ken-burns** | static photos feel dead; a slow drift feels intentional |
| a **sequence / flow / timeline / connection** | a line or `path` with a **`dash-march` loop**, or morph a highlight through the steps | motion carries the eye along the sequence |
| a **headline number** | big text + `fx:{countUp:true}` | the count-up earns attention |
| **every cover / section divider** | at least **one ambient motion** (ken-burns, an orbiting accent) | a still cover is a missed first impression |
| **repeated chrome / a logo** | keep its `id` stable across slides | it morphs in place instead of popping on every slide |
| a **demo clip / recording / soundbite** | a **media** element (embed short, link long) | a live video/audio beats a screenshot of one |

### Copy-paste recipes

**Morph a title + accent bar between two slides** — identical ids, `transition:"morph"`:
```json
// slide 1
{ "id":"s1","transition":"none","elements":[
  { "id":"headline","type":"text","x":96,"y":140,"w":900,"h":200,"html":"Big claim.","fontSize":120,"fontWeight":900,"color":"#111","align":"left","valign":"top","lineHeight":1,"rotation":0,"opacity":1 },
  { "id":"bar","type":"shape","shape":"rect","x":96,"y":380,"w":320,"h":16,"fill":"#E8442E","stroke":"none","strokeWidth":0,"radius":0,"rotation":0,"opacity":1 } ] }
// slide 2 — same ids, new frames → they animate
{ "id":"s2","transition":"morph","elements":[
  { "id":"headline","type":"text","x":96,"y":84,"w":500,"h":80,"html":"Big claim.","fontSize":40,"fontWeight":900,"color":"#888","align":"left","valign":"top","lineHeight":1,"rotation":0,"opacity":1 },
  { "id":"bar","type":"shape","shape":"rect","x":96,"y":170,"w":16,"h":450,"fill":"#E8442E","stroke":"none","strokeWidth":0,"radius":0,"rotation":0,"opacity":1 } ] }
```

**A bar chart from a table** — bar/line data is PLAIN NUMBERS (see chart rules below):
```json
{ "id":"c1","type":"chart","x":96,"y":260,"w":1088,"h":380,"rotation":0,"opacity":1,"preset":"bar","option":{
  "xAxis":{"type":"category","data":["2022","2023","2024","2025"]},
  "yAxis":{"type":"value"},
  "series":[{"type":"bar","data":[420,780,1300,2450],"itemStyle":{"color":"#141310"},"barWidth":90}],
  "tooltip":{"trigger":"item","formatter":"{b}: {c}"} },
  "fx":{"enter":"fade-up"} }
```

**A comparison table** — a real HTML table; cells are the same inline-html subset as text:
```json
{ "id":"tbl1","type":"table","x":240,"y":220,"w":800,"h":260,"rotation":0,"opacity":1,
  "header":true,
  "columns":[{"w":1.4},{"w":1},{"w":1}],
  "rows":[
    { "cells":[{"html":"Plan"},{"html":"Price","align":"right"},{"html":"Seats","align":"right"}] },
    { "cells":[{"html":"Team"},{"html":"$29"},{"html":"5"}] },
    { "cells":[{"html":"Business"},{"html":"$79"},{"html":"25"}] } ],
  "style":{"headerBg":"#1E2A3A","headerColor":"#fff","zebra":"rgba(30,42,58,0.05)",
    "borderColor":"rgba(30,42,58,0.14)","borderWidth":1,"cellPadX":16,"cellPadY":11,
    "fontSize":18,"color":"#1E2A3A","radius":10} }
```

**A state slide reached by clicking a node** — parent slide has the clickable element, the state lives adjacent:
```json
// on the parent slide, an element the viewer clicks:
{ "id":"node-ingest","type":"shape","shape":"ellipse","x":330,"y":180,"w":74,"h":74,"fill":"#0B0E1E","stroke":"#7A5CFF","strokeWidth":2,"radius":0,"rotation":0,"opacity":1,"link":"state-ingest" }
// a hidden state slide (arrow keys skip it; ← returns to parent):
{ "id":"state-ingest","stateOf":"parent-slide-id","transition":"morph","name":"INGEST","elements":[ /* … */
  { "id":"dismiss","type":"shape","shape":"rect","x":0,"y":0,"w":1280,"h":720,"fill":"rgba(0,0,0,0)","stroke":"none","strokeWidth":0,"radius":0,"rotation":0,"opacity":1,"link":"parent-slide-id" } ] }
```

**Full-bleed hero image with ken-burns + scrim + text:**
```json
{ "id":"photo","type":"image","x":0,"y":0,"w":1280,"h":720,"src":"asset:hero","fit":"cover","radius":0,"rotation":0,"opacity":1,"fx":{"ambient":"kenburns","ken":{"dir":"drift","scale":1.09,"duration":22}} },
{ "id":"scrim","type":"shape","shape":"rect","x":0,"y":0,"w":1280,"h":720,"fill":"rgba(10,14,26,0.55)","stroke":"none","strokeWidth":0,"radius":0,"rotation":0,"opacity":1 },
{ "id":"htitle","type":"text","x":96,"y":460,"w":1000,"h":180,"html":"On top of the photo.","fontSize":76,"fontWeight":800,"color":"#fff","align":"left","valign":"top","lineHeight":1.05,"rotation":0,"opacity":1,"fx":{"enter":"fade-up"} }
```
(Embed the image as a data URI in `doc.assets` under key `hero`, then reference `"asset:hero"` — the file must stay self-contained.)

**Video — embed a short clip, or link a big one** (autoplay is present-only; `muted` required to autoplay):
```json
// embedded — self-contained, keep it small (a few MB at most):
{ "id":"clip","type":"media","kind":"video","src":"data:video/mp4;base64,AAAA…","x":220,"y":120,"w":840,"h":472,"rotation":0,"opacity":1,"controls":true,"muted":true,"autoplay":true,"loop":true,"fit":"cover","radius":8 }
// linked — deck stays tiny; needs the URL at play time (give it a poster):
{ "id":"clip","type":"media","kind":"video","src":"https://cdn.example.com/demo.mp4","poster":"asset:demo-poster","x":220,"y":120,"w":840,"h":472,"rotation":0,"opacity":1,"controls":true }
```

### Before you finish — self-audit

- [ ] Any numbers rendered as text that should be a **chart**?
- [ ] Do consecutive slides on one subject share element **ids + `transition:"morph"`**?
- [ ] At least one **motion moment** (ken-burns / loop / count-up), especially the cover?
- [ ] A drill-down that would work better as a **state slide**?
- [ ] One accent colour, at most two typefaces, **96px** side margins (right-most x ≤ 1184)?
- [ ] **Speaker notes** written on each slide (they travel in the file and double as the talk track)?
- [ ] **Have you actually looked at it?** Open the deck and page through every
      slide. Text overflowing its box, two elements crowding each other, a
      heading that wrapped to three lines, a chart key that was silently
      dropped — none of these are visible in the JSON, and all of them are
      obvious on screen. This is the only check that catches what the others
      cannot; a deck nobody rendered is not finished.

### `window.bento.measure()` — size text before you place it

The format is absolute pixels, which is what lets morph, the drag handles and
the renderer work from one representation. The cost falls on you: the height of
a string at a given width and font is not knowable from the JSON. Stop guessing
and ask:

```js
window.bento.measure({ html: 'Long paragraph…', w: 600, fontSize: 28, lineHeight: 1.4 })
// → { height: 236, width: 600, lines: 6 }
```

Pass a spec to size text **before** the element exists — which is the point, as
it lets you lay a slide out correctly the first time. Pass an element id to
measure one already in the deck, and include `h` in a spec to get `fits` and
`overflow` back too. It renders through the real renderer, so the answer is
what the slide will actually do, not an estimate.

Use it for the arithmetic that used to be guesswork: stacking cards in a
column, deciding whether a heading needs two lines or three, sizing a caption
under a photo. In the editor, the same thing is a **Fit height to text** button
in the Typography panel.

### `window.bento.validate()`

Open the deck and run it in the browser console. It reports, in one pass, the
things the runtime otherwise swallows in silence:

```js
const { ok, counts, findings } = window.bento.validate()
findings.filter(f => f.severity !== 'info')
```

Each finding is `{code, severity, message, slide?, element?, path?}`. It checks
unknown property names (a typo is ignored, so the styling just never applies),
text that overflows its box (measured against the real renderer), elements off
the canvas, entrances that can never run, `dash-march` without a dashed stroke,
broken `link` and `asset:` references, duplicate ids and morph-key collisions,
and chart options charts-lite does not implement.

It only reads — it never changes the document, and a finding is advice, not a
refusal. `severity: "info"` is deliberately quiet (a photo bleeding off the
canvas is a design move, not a defect); `error` means something is broken, like
a link to a slide that does not exist.

This does not replace looking at the deck. It catches what is checkable; the
rest — whether a slide is any good — still needs eyes.

## Minimal valid document

Start from this skeleton when creating a deck from scratch. `size` and
`theme` (including `fontFamily`) are **required** — the app will not boot
without them — and elements should carry the full field set shown.

```json
{
  "format": "bento/slides", "version": 1, "title": "My deck",
  "size": { "width": 1280, "height": 720 },
  "theme": { "background": "#101418", "color": "#F2F0EA",
             "accent": "#FF9E8A", "fontFamily": "system-ui, sans-serif" },
  "slides": [
    { "id": "s1", "background": "#101418", "transition": "none",
      "notes": "speaker notes here",
      "elements": [
        { "id": "t1", "type": "text", "x": 96, "y": 260, "w": 1088, "h": 160,
          "rotation": 0, "opacity": 1,
          "html": "Hello from an agent.",
          "fontSize": 88, "fontFamily": "system-ui, sans-serif",
          "fontWeight": 800, "color": "#F2F0EA",
          "align": "left", "valign": "top", "lineHeight": 1.1 }
      ] }
  ]
}
```

## Element types (all share `id,x,y,w,h,rotation,opacity`)

- **text**: `html` (inline `<b> <i> <br>` ok), `fontSize`, `fontFamily`,
  `fontWeight`, `color`, `align` (`left|center|right`), `valign`,
  `lineHeight`, optional `letterSpacing`.
- **shape**: `shape` = `rect|ellipse|triangle|arrow|line|path`, `fill`, `stroke`,
  `strokeWidth`, `radius` (rect corner). Optional `fillGradient`
  `{angle, stops:[{at:0..1, color}]}` (CSS-convention angle). Lines take
  their color from `fill` and draw horizontally across the box (rotate for
  vertical); `strokeStyle: solid|dashed|dotted`; tips `lineStart`/`lineEnd`
  = `arrow|dot|bar`. A `path` is a free vector: `d` (SVG path data) +
  `pathBox` `[x,y,w,h]` authoring viewBox, stretched into the element box;
  for a **curved line** set `fill:"transparent"` + a `stroke` + `strokeWidth`.
  A **connector** is a `line` (or `path`) with `from`/`to: {el, side}` — its ends
  follow those elements and re-route when they move (side `"auto"` picks the
  nearest border). Make sure a shape's colour contrasts with its slide background.
- **image**: `src` = data URI or `"asset:<key>"` into `doc.assets`,
  `fit: cover|contain|fill`, `radius`. Embed images as data URIs in
  `doc.assets` and reference them — the file must stay self-contained.
- **chart**: `preset: bar|line|pie|scatter`, `option` = ECharts-SHAPED pure
  JSON. **Bar/line series data must be plain numbers** (`{value,itemStyle}`
  objects coerce to 0 — only pie takes `{name,value}`); per-item bar colors
  are unsupported, color by series; template formatters only (`{b}`, `{c}`,
  `{d}`), never functions. **Dual axis**: for two series on very different
  scales (e.g. volume + a %), make `yAxis` an ARRAY of two `{type:"value"}`
  axes (give the 2nd `axisLabel:{formatter:"{value}%"}`) and point the odd
  series at it with `"yAxisIndex":1` — render it as a `line` over the bars.
  **The engine is charts-lite, not ECharts** — it reads the option SHAPE and
  ignores every key it does not implement, silently. What it honours:
  - top level — `color`, `series`, `xAxis`, `yAxis`, `legend`, `grid`,
    `tooltip`, `textStyle`, `dataZoom`
  - any series — `type`, `name`, `data`, `yAxisIndex`, `itemStyle.color`
  - bar — `itemStyle.borderRadius`
  - line — `smooth`, `symbol`, `symbolSize`, `lineStyle.color`,
    `lineStyle.width`, `areaStyle.color`
  - pie — `radius`, `label.formatter` (or `label:false`),
    `itemStyle.borderColor`, `itemStyle.borderWidth`
  - axes — `type`, `data`, `min`, `max`, `axisLabel` (`fontSize`,
    `fontWeight`, `color`, `formatter`), `axisLine`, `splitLine`
  - legend — `show`, `top`, `bottom`, `textStyle.fontSize`,
    `textStyle.fontWeight`

  **`label` on a bar or line series does nothing** — value labels above bars
  are pie-only. If you need the numbers visible on a cartesian chart, put them
  in a table beside it, or use text elements.
- **table**: `columns` (array of `{w}` fractional weights), `rows` (array of
  `{cells:[{html, align?, color?, bg?, bold?}]}`), `header` (bool — row 0 is
  the header), and a `style` object (`headerBg`, `headerColor`, `zebra?`,
  `borderColor`, `borderWidth`, `cellPadX`, `cellPadY`, `fontSize`, `color`,
  `radius`). Renders as a real HTML table. Use for comparison/spec/pricing
  grids — NOT for numeric trends (use a chart).
- **svg**: `asset` or `markup` for static artwork. Prefer composing rects/
  texts/paths — those stay editable and can morph.
- **media**: `kind: video|audio`, `src` = data URI (embedded — travels in the
  file), an external URL / relative path (referenced — keeps the file small,
  needs the network at play time), or `"asset:<key>"`. Video also takes
  `poster`, `fit: cover|contain|fill`, `radius`. Playback flags: `controls`,
  `autoplay`, `loop`, `muted`. **Autoplay fires only in present mode**, and
  browsers require `muted:true` for a video to autoplay. **Embed only SHORT
  clips** — a big data URI bloats the file and makes it slow to open/save;
  host large media and reference its URL instead.

## The rules that make decks feel designed

- **Morph = shared ids.** Slides with `"transition": "morph"` tween any
  elements whose `id` matches the previous slide — position, size, color,
  gradients. This is THE signature move: carry 2–4 ids through the deck and
  rearrange them per slide. Generators must emit deterministic ids.
- **`morphId` decouples morph identity from `id`.** The real pairing key is
  `morphId || id`, so an element can keep whatever `id` it likes and set
  `"morphId": "running-head"` to morph against a differently-named element on
  the next slide. For a generator this beats threading one id by hand through
  every slide, and it lets two independently-created elements pair up. The key
  must be unique **within** a slide. Plain shared `id` still works and is still
  the simplest thing when you control both slides.
- **Entrances**: `fx: { enter: "fade-up", order: 0 }` — equal `order` =
  simultaneous. On a **morph arrival** the rule is per element, and it turns on
  whether that element has a morph partner on the previous slide:
  - **has a partner** → it morphs, and `fx.enter` and `fx.countUp` are both
    skipped. It is already in motion and already showing its number; an
    entrance would fight the tween and a count-up would restart from zero.
  - **no partner** → it is new to the slide, so both run normally. Without an
    `fx.enter` it gets an automatic fade-and-rise so nothing ever just pops in.

  So a headline number, or a panel that sweeps in from the right, is fine on a
  morph slide — just make sure it is new to that slide.
- **Ken-burns**: `fx: { ambient: "kenburns", ken: { dir: "drift|out|in",
  scale: 1.08, duration: 20 } }` — `drift` loops, `out`/`in` settle once on
  slide entry. For full-bleed photos: image at 0,0,1280,720 + a scrim rect
  + text on top. Never combine entrance tweens with motion-path loops.
- **Loops**: two shapes, both under `fx.loop`.
  - `{ type: "dash-march", distance: 18, duration: 1.4 }` — marches the stroke
    dashes along a shape. It animates `strokeDashoffset`, so it needs a
    `stroke` **and** a dash pattern: set `strokeStyle: "dashed"` or `"dotted"`.
    On a solid stroke the tween still runs and there is nothing to see.
  - `{ type: "motion-path", path: "M0,0 C60,-40 140,40 200,0", duration: 6,
    delay: 0, ease: "none", speeds: [1, 1] }` — drifts the element along a
    path given RELATIVE to its resting position (the first anchor is where it
    sits). `speeds` is optional, one multiplier per on-curve point, and lets
    the element dwell in places and rush others; omit it for constant pace.
    Never put an entrance tween on a motion-path element — they fight over the
    same transform.
- **Interactivity**: element `link: "<slide-id>"` jumps on click; a slide
  with `stateOf: "<parent-id>"` is a hidden variant reached only by links
  (arrow keys skip it, ← returns to parent). Give clickable things a padded
  transparent rect as the hit target, not the text itself.
- **Hidden slides**: `"hidden": true` keeps a slide in the deck and out of the
  show — arrow keys skip it, PDF export leaves it out, and it is never the
  file's thumbnail — but an element `link` still reaches it. That is what it is
  for: backup and appendix material you jump to only if asked. By default a
  hidden slide does not consume a page number either, so `{{page}}`/`{{pages}}`
  stay contiguous for the audience; set `present.numberHidden: true` for the
  office-suite behaviour where it keeps its number.

  Not the same as `stateOf`. A state is a variant OF another slide (← returns
  to its parent, and it morphs with it); hidden carries no such relationship.
  Use a state for "click to drill into this", hidden for "only if they ask".
- **Numbers count up** with `fx: { countUp: true }`.
- **Speaker notes** (`notes`) are part of the document — write them; they
  make a template teach itself.

## Layout guardrails

- Canonical canvas 1280×720 (`doc.size` can differ — read it first).
- Keep 96 px side margins (right-most content x ≤ 1184).
- **Column arithmetic, already done.** On 1280×720 inside 96 px margins the
  content band is 1088 px wide. Use these rather than computing your own:

  | Split | Width | `x` positions | Gutter |
  |---|---|---|---|
  | 2 columns | 528 | 96, 656 | 32 |
  | 3 columns | 340 | 96, 470, 844 | 34 |
  | 4 columns | 254 | 96, 374, 652, 930 | 24 |
  | 60 / 40 (text + image) | 624 / 432 | 96, 752 | 32 |

  Every row ends flush at x = 1184. Vertically, a title band of `y:72 h:84`
  over content starting at `y:208` leaves 416 px of content height above a
  96 px bottom margin.
- One accent color; 2 typefaces max. `theme` sets deck defaults.
- Fonts: `doc.fonts` (`{family, asset, weight}`) + woff2 data URIs in
  `doc.assets` if you need embedded faces; otherwise stick to system stacks.
  **A `fontFamily` naming a face the document does not carry falls back
  silently** to the next entry in the stack — there is no warning, and worse,
  it will usually look right to *you*, because you are the one with the
  typeface installed. Everyone else gets the fallback. `validate()` reports
  this (`font-not-embedded`) precisely because you cannot see it locally.
  Fonts belong to the DOCUMENT, not the app:
  Instrument Sans and Fraunces appear in the starter deck and in several
  templates because those files embed them in their own `doc.assets`, not
  because the app provides them. So either embed the woff2 yourself, start from
  a template that already carries the face, or name a system stack and mean it.
  Always write a full stack (`"'Fraunces', Georgia, serif"`), never a bare
  family name.

## Layouts and `role`

`doc.layouts` is a supported top-level key: an array of Slide-shaped templates
the editor offers under *Apply layout*. Every deck also gets five built-ins
(`layout-title`, `layout-title-content`, `layout-two-col`, `layout-section`,
`layout-blank`), which are scaled to the deck's `doc.size` when applied.

The part that matters when you are generating a deck is **`role`**. Any text
element can carry `"role": "title" | "subtitle" | "body" | "kicker"`. Applying a
layout matches donor to target by `id` first and then by `role` + `type`, so
roles are what let someone restyle your deck later without re-typing it —
content rides across, the layout supplies frame and typography. Setting them
costs one key per element and makes a generated deck feel native to the editor.

Two smaller things: a layout's text elements use `placeholder` (a dimmed prompt
shown in the editor, hidden in present and print) rather than `html`, and
slides instantiated from the same layout keep their element ids — which is
exactly why their furniture morphs across a transition.

## Dynamic fields (tokens in text `html`)

Put these tokens in any text element's `html`; they resolve at render time (the
model keeps the raw token, so numbering/props update automatically):
`{{page}}`, `{{pages}}` (position among non-state slides; zero-pad with
`{{page:2}}`→"06"), `{{title}}`, `{{date}}`, `{{time}}`, and the document
properties `{{author}}`, `{{company}}`, `{{subject}}`, `{{event}}`. Set the
props in an optional top-level `"meta": {author, company, subject, event,
keywords}` object — great for title slides and footers that fill from one place.

## Gotchas

- Escape `<` as `\u003c` anywhere in the JSON when writing the file block.
- Don't invent property names — unknown keys are ignored, so a typo means
  your styling silently doesn't apply.
- `docId` is the document's identity — never regenerate it when editing.
- `readonly: true` makes a PLAYER file — it boots straight into the
  presentation with no editor. Set it only on hand-out copies.
- If `template: true` is set, every open mints a fresh document (that's for
  distributable templates; remove it for a personal deck).
- Charts degrade gracefully but anything outside the list in the **chart**
  element type above is ignored, with no warning — keep options minimal and
  check the rendered slide rather than trusting the JSON.
- **Media size**: embedding a large video as a data URI can push the file into
  the tens of MB and make it slow to open and save. Embed only short clips;
  otherwise host the file and put its URL in `media.src`.

Working examples of everything above: the template decks at
[bento.page](https://bento.page) — open one and read its JSON block.
