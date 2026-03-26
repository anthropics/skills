---
name: decksmith-presentations
description: >
  Create interactive HTML presentations using the Decksmith Svelte 5 framework.
  Use this skill when the user asks to create, generate, edit, or modify a Decksmith
  presentation, slideshow, or slide deck. Trigger when the user mentions "presentation,"
  "slides," "slide deck," "slideshow," or "Decksmith," or asks to edit src/App.svelte
  in a Decksmith project.
---

# Decksmith Presentation Skill

Create presentations by generating a single Svelte component (`src/App.svelte`) that uses Decksmith's `<Deck>`, `<Slide>`, `<Fragment>`, `<Notes>`, `<Markdown>`, and `<Code>` components.

## Quick Start

```svelte
<script lang="ts">
  import { Deck, Slide, Fragment, Notes, Markdown, Code } from "decksmith";
</script>

<Deck theme="obsidian" transition="slide">
  <Slide h={0} v={0}>
    <h1>Title</h1>
    <p>Subtitle</p>
    <Notes text="Speaker notes for this slide." />
  </Slide>

  <Slide h={1} v={0}>
    <h2>Second Slide</h2>
    <Fragment index={0} style="fade-up">
      <p>First point</p>
    </Fragment>
    <Fragment index={1} style="fade-up">
      <p>Second point</p>
    </Fragment>
  </Slide>
</Deck>
```

Run with `npm install && npm start`, then open http://localhost:5173.

## Rules for Code Generation

1. **Every `<Slide>` must have `h` and `v` props.** The first slide is always `h={0} v={0}`.
2. **`h` values must be sequential** starting from 0. No gaps allowed.
3. **`v` values must start at 0** for each `h` column and increment: `v={0}`, `v={1}`, `v={2}`.
4. **Fragment `index` values start at 0** and increment sequentially within a slide.
5. **One `<Deck>` per presentation.** All `<Slide>` components must be direct children of `<Deck>`.
6. **Use valid prop values only.** See the Component API below.
7. **Inline styles only.** Do not generate `<style>` blocks unless specifically needed for global selectors.
8. **Escape backticks in template literals.** When `code` or `content` props contain backticks, escape them: `` \` ``.
9. **Import only what you use.** Import from `"decksmith"` and include only the components used in the code (for example: `import { Deck, Slide } from "decksmith";`).
10. **Return complete files.** Never return partial snippets when editing — always the full `src/App.svelte`.

## Slide Coordinate System

Slides are arranged in a 2D grid:

```
h=0,v=0  →  h=1,v=0  →  h=2,v=0  →  h=3,v=0
                         ↓
                         h=2,v=1
                         ↓
                         h=2,v=2
```

- `h` increments left-to-right for the main sequence.
- `v` increments top-to-bottom for sub-slides under a given `h`.
- Vertical slides (v > 0) are navigated with ↑/↓ keys.

## Component API

### `<Deck>` — Root Container

| Prop              | Type                                                             | Default      | Description                    |
| ----------------- | ---------------------------------------------------------------- | ------------ | ------------------------------ |
| `theme`           | `"obsidian" \| "air" \| "dusk" \| "parchment" \| "ember"`        | `"obsidian"` | Visual theme                   |
| `transition`      | `"none" \| "fade" \| "slide" \| "convex" \| "concave" \| "zoom"` | `"slide"`    | Default slide transition       |
| `transitionSpeed` | `"default" \| "fast" \| "slow"`                                  | `"default"`  | Transition duration            |
| `width`           | `number`                                                         | `960`        | Base slide width in px         |
| `height`          | `number`                                                         | `700`        | Base slide height in px        |
| `controls`        | `boolean`                                                        | `true`       | Show navigation arrows         |
| `progress`        | `boolean`                                                        | `true`       | Show progress bar              |
| `slideNumber`     | `boolean`                                                        | `true`       | Show slide number              |
| `hash`            | `boolean`                                                        | `true`       | URL hash routing               |
| `overview`        | `boolean`                                                        | `true`       | Enable overview mode (Esc key) |
| `touch`           | `boolean`                                                        | `true`       | Enable touch/swipe navigation  |
| `keyboard`        | `boolean`                                                        | `true`       | Enable keyboard navigation     |
| `loop`            | `boolean`                                                        | `false`      | Loop from last slide to first  |
| `scrollView`      | `boolean`                                                        | `false`      | Scrollable page mode           |
| `scrollLayout`    | `"full" \| "compact"`                                            | `"full"`     | Scroll slide sizing            |
| `scrollSnap`      | `boolean`                                                        | `true`       | CSS scroll-snap in scroll view |

### `<Slide>` — Individual Slide

| Prop                 | Type             | Default      | Description                      |
| -------------------- | ---------------- | ------------ | -------------------------------- |
| `h`                  | `number`         | `0`          | Horizontal position              |
| `v`                  | `number`         | `0`          | Vertical position                |
| `transition`         | `TransitionType` | _(inherits)_ | Override transition              |
| `background`         | `string`         | `""`         | CSS background (color, gradient) |
| `backgroundImage`    | `string`         | `""`         | Background image URL             |
| `backgroundSize`     | `string`         | `"cover"`    | CSS background-size              |
| `backgroundPosition` | `string`         | `"center"`   | CSS background-position          |
| `id`                 | `string`         | —            | Optional slide identifier        |
| `autoAnimate`        | `boolean`        | `false`      | Enable auto-animate              |

### `<Fragment>` — Step-by-Step Reveal

| Prop    | Type            | Default     | Description                     |
| ------- | --------------- | ----------- | ------------------------------- |
| `index` | `number`        | `0`         | Order of appearance (0 = first) |
| `style` | `FragmentStyle` | `"fade-in"` | Animation style                 |

**Fragment styles:** `fade-in`, `fade-out`, `fade-up`, `fade-down`, `fade-left`, `fade-right`, `fade-in-then-out`, `fade-in-then-semi-out`, `grow`, `shrink`, `strike`, `highlight-red`, `highlight-green`, `highlight-blue`, `highlight-current-red`, `highlight-current-green`, `highlight-current-blue`

### `<Notes>` — Speaker Notes

| Prop      | Type     | Default | Description                                                                 |
| --------- | -------- | ------- | --------------------------------------------------------------------------- |
| `text`    | `string` | `""`    | Speaker notes content                                                       |
| `slideH`  | `number` | `0`     | Horizontal slide index (must match the slide's `h` when attaching notes)    |
| `slideV`  | `number` | `0`     | Vertical slide index (must match the slide's `v` when attaching notes)      |

When generating notes for a slide, always set `slideH` and `slideV` to that slide's `h`/`v` coordinates so the notes attach to the correct slide.
### `<Markdown>` — Markdown Content

| Prop      | Type     | Default | Description               |
| --------- | -------- | ------- | ------------------------- |
| `content` | `string` | `""`    | Markdown string to render |

### `<Code>` — Syntax-Highlighted Code

| Prop              | Type      | Default  | Description                                        |
| ----------------- | --------- | -------- | -------------------------------------------------- |
| `code`            | `string`  | `""`     | Code to display                                    |
| `language`        | `string`  | _(auto)_ | Language for highlighting                          |
| `lineNumbers`     | `boolean` | `false`  | Show line numbers                                  |
| `highlightLines`  | `string`  | `""`     | Line highlight steps (pipe-separated, comma-aware) |
| `lineNumberStart` | `number`  | `1`      | Starting line number                               |

`highlightLines` format: `"1|2-3|4,6-10"` — pipe-separated steps; within each step, use commas to combine single line numbers and ranges.

## Theme Selection

| Audience / Context   | Recommended Theme    |
| -------------------- | -------------------- |
| Tech conference      | `obsidian` or `dusk` |
| Business / corporate | `parchment` or `air` |
| Academic / research  | `air` or `parchment` |
| Creative / bold      | `ember`              |
| General purpose      | `obsidian`           |

## Transition Selection

| Content Type             | Recommended Transition               |
| ------------------------ | ------------------------------------ |
| Technical / code-heavy   | `none` or `fade`                     |
| Storytelling / narrative | `slide`                              |
| Dramatic reveals         | `zoom`                               |
| Professional / polished  | `convex` or `concave`                |
| Fast-paced               | `fade` with `transitionSpeed="fast"` |

## Generation Workflow

Given a user prompt like "Create a 5-slide presentation about microservices":

1. **Plan the structure**: Title, 3 content slides, closing
2. **Assign coordinates**: h=0 through h=4, all v=0
3. **Choose theme**: Match the audience/context
4. **Choose transition**: Match the content type
5. **Generate each slide** using patterns below
6. **Add fragments** for bullet points (2-4 per slide)
7. **Add speaker notes** for key slides
8. **Include a code example** if relevant

## Slide Patterns

### Title Slide

```svelte
<Slide h={0} v={0}>
  <h1>Presentation Title</h1>
  <p>Subtitle or author name</p>
  <Notes text="Speaker notes here." />
</Slide>
```

### Bullet Points with Fragments

```svelte
<Slide h={N} v={0}>
  <h2>Key Points</h2>
  <Fragment index={0} style="fade-up"><p>First point</p></Fragment>
  <Fragment index={1} style="fade-up"><p>Second point</p></Fragment>
  <Fragment index={2} style="fade-up"><p>Third point</p></Fragment>
</Slide>
```

### Code Walkthrough

```svelte
<Slide h={N} v={0}>
  <h2>Code Example</h2>
  <Code
    language="typescript"
    lineNumbers
    highlightLines="1-2|4-6|8"
    code={`const greeting = "Hello";
console.log(greeting);

function add(a: number, b: number) {
  return a + b;
}

add(1, 2);`}
  />
</Slide>
```

### Two-Column Layout

```svelte
<Slide h={N} v={0}>
  <h2>Comparison</h2>
  <div style="display: flex; gap: 2em; margin-top: 1em; text-align: left;">
    <div style="flex: 1;">
      <h3>Before</h3>
      <p>Old approach</p>
    </div>
    <div style="flex: 1;">
      <h3>After</h3>
      <p>New approach</p>
    </div>
  </div>
</Slide>
```

### Background Image Slide

```svelte
<Slide h={N} v={0} backgroundImage="/images/photo.jpg" backgroundSize="cover">
  <h1 style="text-shadow: 0 2px 10px rgba(0,0,0,0.5);">Over an Image</h1>
</Slide>
```

### Gradient Background

```svelte
<Slide
  h={N}
  v={0}
  background="linear-gradient(135deg, #667eea 0%, #764ba2 100%)"
>
  <h2>Gradient Slide</h2>
</Slide>
```

### Vertical Sub-Slides

```svelte
<Slide h={N} v={0}>
  <h2>Main Topic</h2>
  <p>Press ↓ for details</p>
</Slide>
<Slide h={N} v={1}>
  <h3>Detail 1</h3>
</Slide>
<Slide h={N} v={2}>
  <h3>Detail 2</h3>
</Slide>
```

### Markdown Slide

```svelte
<Slide h={N} v={0}>
  <Markdown
    content={`
## Features

- **Bold** and *italic* text
- \`inline code\`
- [Links](https://example.com)
  `}
  />
</Slide>
```

### Auto-Animate Between Slides

```svelte
<Slide h={N} v={0} autoAnimate>
  <div
    data-id="box"
    style="width: 100px; height: 100px; background: var(--ds-accent);"
  ></div>
  <h2 data-id="title">Hello</h2>
</Slide>
<Slide h={N + 1} v={0} autoAnimate>
  <div
    data-id="box"
    style="width: 200px; height: 200px; background: var(--ds-accent); border-radius: 50%;"
  ></div>
  <h2 data-id="title" style="font-size: 2.5em;">Hello!</h2>
</Slide>
```

### Closing Slide

```svelte
<Slide h={LAST} v={0} background="linear-gradient(135deg, #0c0c1d, #1a1a3e)">
  <h1>Thank You</h1>
  <p style="margin-top: 0.5em; opacity: 0.7;">Questions?</p>
</Slide>
```

## Editing Existing Presentations

1. **Preserve the overall structure** — don't change slide coordinates unless adding/removing slides
2. **When adding slides**, increment `h` values and renumber all subsequent slides
3. **When removing slides**, renumber `h` values to close gaps
4. **When editing text**, replace only the text content, preserving the surrounding component structure
5. **When changing animations**, only modify the `style` prop on `<Fragment>` or `transition` prop on `<Deck>`/`<Slide>`
6. **Return the complete file** — never return partial snippets
