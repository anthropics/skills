# Speaker Script Rules (Speaker Script.md)

Goal: the presenter can **read the script aloud word for word** and it still sounds like a natural talk.

## Structure
- At the top: total estimated time, and the margin/overrun against the talk length from Step 0
- One section per page: `## p.{n} — {slide title} (about {N} s)`
- Page numbers match the deck's actual page numbers. Renumber when slides are added or removed.

## Style
- Full sentences meant to be read aloud throughout. No bullet fragments, no noun-phrase endings, no casual register.
- If the slides are in English and the script is not: the page title stays as the English slide title, and each English term on screen (axis names, table headers, emphasized phrases) is read aloud once, as is, inside the sentence so the audience can match it to the screen.

## Sound like a person — not like an AI
- Give the sentences rhythm. A long sentence after a short one, and now and then a single word ("Right.", "But.").
- Do not repeat the same transition line on every page ("Now let's look at ~"). Let the question raised on the previous page become the first sentence of the next ("And errors that can't be expressed as parameters? That's the second paper.").
- Do not use enumeration and emphasis scaffolding like "first, second, third", "the key point is", "what's notable is". Speak from the presenter's point of view instead ("The row I kept coming back to in this table is", "Honestly, this one didn't work.").
- Do not read every number; they are on the screen. Read at most 3–4 numbers aloud per page. Turn the rest into words ("less than half", "a six-fold gap").
- Draw on context shared with the audience ("You've all felt this", "Our condition C is randomized, remember").
- Match the register to the venue: a study group or lab seminar sounds natural in a relaxed conversational register; a formal seminar or class keeps a consistently formal one.
- If everything is smooth, it feels wrong. Alternate, page by page, a request for the audience's patience, an honest admission of a limitation, or a single analogy.

## Easy to read aloud
- Spell out symbols and brackets as words: "30%" → "30 percent", "A → B" → "from A to B"
- Write equations the way they are spoken: "theta hat is the action the policy outputs"
- The first time an acronym appears, say how it is read and what it means; afterwards use the acronym only
- One sentence per breath (roughly 15 words, or 40 characters in Korean)
- Do not add content that is not on the slides; explain in slide order

## Stage directions — like a stage play
- Insert **stage directions in parentheses** `( )` between lines: what the presenter is doing at that moment — where they point, where they look, when they click or play, where they pause.
- Put the direction on the same line as the spoken text, at the point where the action happens. Do not break it out onto its own line.
- 2–4 per page. None on a page is too few; one in every sentence is hard to read.
- Kinds of directions:
  - Pointing — `(pointing at the Heavy DR row of the table)`, `(pointing at figure (a) on the left of the screen)`
  - Gaze — `(glancing around the audience)`, `(looking at the screen)`, `(looking at the front row)`
  - Operation — `(click, next slide)`, `(play the left video)`, `(when the video ends)`
  - Breath — `(pause)`, `(a beat)`
  - Gesture — `(moving a hand from left to right)`, `(spreading both hands apart)`
- Write so that the sentences still flow naturally if the parentheses are skipped.

## Transitions
- The last sentence of each page leads into the next page (e.g. "So how did they solve this? Let's see on the next slide.")
- In bundle mode, insert a sentence linking back to the previous paper whenever the paper changes

## Length
- Allocate seconds per page to fit the Step 0 talk length (budget roughly 130–150 words per minute in English, about 300 characters per minute in Korean)
- Keep Title, Outline and References short; give more time to Method and Experiments

## Example
```
## p.5 — Proposed Method (about 60 s)

(glancing around the audience) The core idea of this paper is that it trains in two stages.
(pointing at the left block on the screen) First, in the simulator, it trains a policy that knows everything about the environment.
(moving a hand to the right block) Then it trains a second policy to imitate that one using only what the real robot can observe.
(pause) Put simply, a teacher who has seen the answer key is tutoring the student.
So how well does this actually work on a real robot? That's the next slide. (click)
```
