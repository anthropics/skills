---
name: docs-to-course
description: "Turn any documentation into a beautiful, interactive single-page HTML training course. Use this skill whenever someone wants to create a course, tutorial, or learning artifact from documentation, specs, RFCs, wikis, API references, whitepapers, or any technical writing. Also trigger when users mention 'turn this doc into a course,' 'make training from this,' 'create a tutorial from this spec,' 'interactive course from documentation,' 'teach this RFC,' 'onboarding from docs,' or 'learn from this documentation.' This skill produces a stunning, self-contained HTML file with scroll-based navigation, animated concept visualizations, embedded quizzes, and spec-language-to-plain-English side-by-side translations."
license: MIT. LICENSE file has complete terms.
compatibility: Requires the Firecrawl MCP server (firecrawl-mcp) for URL inputs. Works without it for local files and GitHub repos.
---

# Docs-to-Course

Transform any documentation into a stunning, interactive single-page HTML training course. The output is a single self-contained HTML file (no dependencies except Google Fonts) that teaches the material through scroll-based modules, animated concept visualizations, formative and summative quizzes, spaced retrieval callbacks, and plain-English translations of dense spec language.

Works with: Markdown files, PDFs, RFCs, API reference docs, architecture decision records, wikis, whitepapers, onboarding guides, standards documents, internal runbooks, product specs — any written documentation. **Also works directly from documentation websites** via built-in crawling (Phase 0).

## First-Run Welcome

When the skill is first triggered and the user hasn't specified documentation yet, introduce yourself:

> **I can turn any documentation into an interactive training course — no teaching experience required.**
>
> Just point me at your docs:
> - **A website URL** — e.g., "make a course from https://docs.example.com" — I'll crawl the site automatically
> - **A local folder** — e.g., "turn ./docs into a course"
> - **A single file** — e.g., "make a course from RFC 9460" or "turn this spec.md into a course"
> - **A GitHub link** — e.g., "make a course from https://github.com/user/repo/wiki"
> - **The current project** — just say "turn the docs into a course"
>
> I'll read the documentation, identify the 20% that provides 80% of the practical value, and generate a beautiful single-page HTML course with concept diagrams, plain-English spec translations, and scenario quizzes. The whole thing runs in your browser — no setup needed.

If the user provides a GitHub link, clone or fetch the relevant files first. If they say "this project's docs," look for a `docs/` folder, `README.md`, wiki pages, or any `.md`/`.rst`/`.txt` files in the current working directory.

---

## The Process (5 Phases)

**Phase 0 only runs when the input is a website URL.** For local files or GitHub repos, skip straight to Phase 1.

### Phase 0: Web Crawl via Firecrawl MCP (URL input only)

When the user provides an `https://` URL, **read `references/firecrawl.md`** before proceeding. It contains the full crawl procedure: site mapping, URL filtering rules, batch scrape arguments, credit accounting, and the exact user-facing messages at each step.

If the Firecrawl tools are not available in your environment, the reference file also has the one-time setup instructions to share with the user. Local files and GitHub repos work without Firecrawl — skip straight to Phase 1 in that case.

After Phase 0, treat each fetched page's markdown as a document and proceed to Phase 1. Record the source URL for each page so spec translation blocks can cite the exact page later.

---

### Phase 1: Analysis — Learner, Scope, and Content

Do all three sub-phases before writing any HTML or designing any curriculum.

#### 1A: Identify the Primary Learner

Pick **one** primary learner profile. A course designed for everyone serves no one. Common profiles for documentation:

| Profile | What they already know | What they need to leave with |
|---|---|---|
| New practitioner | Domain basics, not this system | Mental model + vocabulary to work independently |
| Adjacent-field expert | Deep expertise nearby, not here | Tradeoffs and key differences from what they know |
| Implementer | Conceptual understanding | Precise rules, edge cases, failure modes |
| Decision-maker / lead | Business context | Enough depth to ask the right questions and evaluate options |
| Operator / oncall | How to use it, not why | Why it works this way + what to do when it breaks |

**Write a one-paragraph learner profile:** who this person is, what they already know confidently, what they don't know, and what they need to be able to do after the course. Every content and design decision flows from this. Post it at the top of your internal curriculum plan before continuing.

If the user has specified an audience, use it. Otherwise, infer from the documentation itself: an RFC is written for implementers, an API reference for integrators, an ADR for team engineers, a runbook for operators.

#### 1B: Scope the Course

Large documentation sets cannot become a single course without scoping. Apply the 80/20 rule: **identify the 20% of the documentation that provides 80% of the practical value** for the primary learner. Everything else is reference material they can look up — don't teach it.

**Scoping heuristics:**
- A single HTML course should take **15–25 minutes per module** to complete, with 5–7 modules maximum
- If the documentation has more material than 5–7 modules can cover well, scope to the core flow and note what's excluded
- Prioritize: concepts required to understand anything else → the main operational flow → the most common edge cases → the most dangerous gotchas
- Cut: exhaustive option reference, historical rationale that doesn't affect current behavior, content the learner will look up rather than internalize

**Document your scope decision:** write one sentence for each major section of the documentation — "include (core flow)," "include (edge case, high risk)," or "exclude (reference, low teaching value)."

#### 1C: Analyze the Content

Now read the scoped documentation deeply. Extract:

- **The core problem** — what situation or need does this address? What goes wrong without it?
- **The key concepts** — the 3–7 ideas someone must hold in their head for everything else to make sense
- **Prerequisite knowledge map** — what does the documentation assume the reader already knows? What gaps might the primary learner have?
- **The mental model** — how do the pieces fit together? Map the relationships, not just the inventory.
- **Technical vocabulary** — terms used with a precise meaning in this document, especially terms that look familiar but differ from everyday usage or adjacent-field usage
- **The tradeoffs** — every design decision trades something. What did the authors choose and why?
- **The gotchas** — mistakes practitioners commonly make; things the doc warns about; failure modes
- **The "so what"** — after understanding this, what can the learner now do that they couldn't before?

**Adjust analysis focus by document type:**

| Document type | Primary analysis focus |
|---|---|
| RFC / standards document | Problem statement, protocol flow, MUST/SHOULD/MAY distinctions, security considerations, edge cases |
| API reference | Authentication, core data model, common call patterns, error handling, rate limits |
| Architecture doc / ADR | Decision made, alternatives considered, tradeoffs, when to revisit |
| Onboarding guide | System mental model, key operations, common first-week mistakes |
| Runbook / operational guide | Action sequences, decision points, what can go wrong and how to recover |
| Whitepaper | The claim, the evidence, the assumptions, the practitioner implications |

---

### Phase 2: Curriculum Design

#### 2A: Write Learning Objectives First

Before designing any module's content, write **1–3 learning objectives** for each module. Objectives must be:

- **Measurable** — start with an action verb from Bloom's taxonomy
- **Specific** — describe what the learner will be able to do with the knowledge, not just that they'll "understand" it
- **Pitched at application or above** — avoid "remember" and "understand" objectives; favor "apply," "analyze," "evaluate," and "create"

**Bloom's verb reference (use these):**

| Level | Verbs to use |
|---|---|
| Apply (L3) | implement, use, execute, solve, demonstrate, apply |
| Analyze (L4) | differentiate, compare, distinguish, examine, break down, trace |
| Evaluate (L5) | judge, justify, defend, critique, assess, select (given criteria) |
| Create (L6) | design, construct, compose, propose, formulate |

**Avoid:** "understand," "know," "learn," "appreciate," "be familiar with" — these are not measurable.

**Example objectives (from a DNS TTL course):**
- *Apply*: Given a DNS response with a specific TTL, determine the correct caching behavior at each resolver type.
- *Analyze*: Given a broken DNS propagation scenario, trace which component is most likely at fault and why.
- *Evaluate*: Given two TTL strategies for a high-availability service, select the better one and justify the tradeoff.

**Check alignment:** once objectives are written, verify that your planned content actually teaches each objective and that your planned quiz question actually tests it. If content doesn't connect to an objective, cut it or add an objective. If an objective has no quiz question, write one.

#### 2B: Design the Curriculum Arc

Structure the course as 5–7 modules plus a required synthesis module. The arc always starts from **why this matters** and moves toward **how to apply it**, ending with a synthesis that connects all the pieces.

| Module position | Purpose | Instructional strategy |
|---|---|---|
| 1 | The problem and the big picture | Hook with a concrete failure scenario; establish why this exists |
| 2 | Key concepts and vocabulary | Pre-train components in isolation before showing them working together |
| 3 | The core flow | Trace end-to-end with a worked example; then a faded example |
| 4 | The important details | Segment into sub-flows; address edge cases that affect the primary learner |
| 5 | Design decisions and tradeoffs | Evaluate alternatives; build judgment, not just knowledge |
| 6 | Applying it in practice | Transfer activity: new scenario the learner hasn't seen |
| 7 (optional) | When things go wrong | Debugging mental model; failure modes; recovery patterns |
| Final | Synthesis and closure | Reassemble the full mental model; return to Module 1's opening scenario |

**Scaffolding between modules:**
- End every module with a one-sentence bridge: *"In the next module, we'll see what happens when this mechanism meets [complication]."*
- Begin every module from Module 2 onward with a **prerequisite signal**: *"This module assumes you understand [concept from previous module]. If that's fuzzy, scroll back to Module N."*
- From Module 3 onward, include one **retrieval callback** per module — a question or reference that resurfaces a concept from an earlier module in a new context.

**Each module must contain:**
- 1–3 learning objectives (written in Phase 2A)
- A **prerequisite signal** (Modules 2+)
- 3–6 screens, each teaching exactly one idea
- At least one **spec-to-plain-English translation**
- At least one **formative check** embedded mid-module (prediction question, inline knowledge check, or completion problem)
- At least one **interactive element** (see reference files)
- One or two **"aha!" callout boxes** — insights the doc never states directly but practitioners learn the hard way
- At least one **metaphor**, followed immediately by its boundary (*"This analogy breaks down when X, because in reality Y"*)
- A **summative quiz** at the end (3–5 scenario-based questions)
- A **retrieval callback** (Modules 3+)
- A **bridge sentence** to the next module

**Do NOT present the curriculum for approval — build it.** Design internally, generate the HTML, let the user react to the result.

---

### Phase 3: Build the Course

Generate a single HTML file with embedded CSS and JavaScript. Read `references/design-system.md` for the complete CSS design tokens, typography, accessibility requirements, and color system. Read `references/interactive-elements.md` for implementation patterns of every interactive element type.

#### 3A: Accessibility baseline (non-negotiable)

Every course must meet WCAG 2.1 AA as a floor. Read the accessibility section of `references/design-system.md` before writing any HTML. Required at minimum:

- All text meets contrast ratio requirements (4.5:1 body, 3:1 large text)
- All interactive elements have `aria-label` or visible label and correct `role`
- All diagrams and visual-only content have descriptive `alt` text or `aria-label`
- All interactive elements are keyboard-operable (tab, enter, space, arrow keys)
- Focus states are always visible — never `outline: none` without a replacement
- Drag-and-drop has a keyboard-accessible fallback (click-to-select, click-to-place)
- Tooltips are dismissible by keyboard (Escape key)
- Color is never the only means of conveying information (always pair with text or icon)

#### 3B: Build order

1. **Foundation** — HTML shell with all module sections (empty), complete CSS design system, navigation bar with progress tracking, scroll-snap behavior, keyboard navigation, and scroll-triggered animations. After this step, you have a working skeleton.

2. **One module at a time** — For each module:
   a. Write the prerequisite signal and learning objectives display
   b. Build the content screens
   c. Add formative checks (prediction question or completion problem)
   d. Add the spec translation block(s)
   e. Add the retrieval callback (Module 3+)
   f. Add the summative quiz
   g. Add the bridge sentence

3. **Synthesis module** — Build last, after all content modules exist. See synthesis module spec below.

4. **Polish pass** — transitions, mobile responsiveness, visual consistency, accessibility audit.

#### 3C: The synthesis module (required)

Every course must end with a synthesis module. It is **not** a summary — it is a reassembly. Structure:

1. **Return to the opening scenario** — restate the concrete problem or failure from Module 1. Now ask the learner to solve it with everything they've learned. This is the highest-value transfer activity in the course.

2. **The assembled mental model** — show the complete concept map, architecture diagram, or flow diagram that represents the whole system. Each piece should be recognizable from a specific earlier module. Clicking or hovering a component links back to where it was taught.

3. **What you can now do** — 3–5 concrete capabilities the learner has gained, phrased as actions: *"You can now trace a DNS propagation failure to its source," not "You now understand DNS propagation."*

4. **Where to go next** — a reference card or checklist the learner keeps: the 5 things to remember, the 3 most dangerous gotchas, the 2 tradeoffs to revisit when making a decision.

5. **A final transfer question** — one open-ended scenario the learner should be able to reason through now. No answer provided — this is for reflection, not grading.

#### 3D: Critical implementation rules

- File must be completely self-contained (only external dependency: Google Fonts CDN)
- Use CSS `scroll-snap-type: y proximity` (NOT `mandatory`)
- Use `min-height: 100dvh` with `100vh` fallback
- Only animate `transform` and `opacity` for GPU performance
- Wrap all JS in an IIFE; use `passive: true` on scroll listeners; throttle with `requestAnimationFrame`
- Include touch support for drag-and-drop; keyboard nav (arrow keys); ARIA attributes throughout

#### 3E: Voice & writing rules (humanizer pass — required before output)

All prose in the generated HTML must pass these rules. Apply them while writing content, then do a final pass before closing `</body>`. When uncertain, invoke the `humanizer` skill on a draft section.

**Banned constructions — fix every instance:**

| Pattern | Example to avoid | Fix |
|---|---|---|
| Em dash in prose | `detects threats — surfacing them as tickets` | Use a colon, comma, or split the sentence |
| Significance inflation | `pivotal, crucial, key, invaluable, vital, testament, underscores` | Use plain words: important, useful, shows, proves |
| Copula avoidance | `serves as, stands as, represents, functions as` | Use `is`, `are`, `works as` |
| Negative parallelism | `not just X, but Y` · `it's not about X, it's about Y` | Say the thing directly |
| False ranges | `from detection to takedown, from alerts to hunting` | List the items explicitly |
| Promotional language | `powerful, seamless, stunning, robust, groundbreaking` | Cut it or replace with a specific claim |
| -ing padding | `...ensuring compliance, highlighting the risk, showcasing how` | Restructure or cut the participial phrase |
| Generic upbeat endings | `the future looks bright · you're on your way · exciting times ahead` | End with a concrete next action |
| Vague attributions | `experts argue, research shows, industry consensus` | Cite the actual source or cut |
| Sycophantic feedback | `Great job! Excellent thinking!` | Just give the feedback |

**Rules for quiz and prediction text specifically:**

- Wrong-answer feedback must never start with "Not quite" or "That's not right" — vary the opening; don't make it sound automated
- Correct-answer feedback must not start with "Correct!" or "Exactly right!" — just explain the concept directly
- Prediction commit button text: use "Lock in my answer →" (single select) or "Lock in my answers →" (multi-select). Never "Submit" or "Confirm"
- Prediction reveals should start with the surprise, not a preamble ("All four — and that's the problem" not "The correct answer is all four")

**Voice baseline for educational content:**

Write like a knowledgeable colleague talking to a smart peer, not like documentation. Sentences can be short. Opinions are allowed. If something has a counterintuitive behavior, say so — "This surprises most people." If something is genuinely tricky, say so — "This is the one that trips up experienced analysts." Avoid sounding assembled.

---

## Content Philosophy

### Objectives-First, Then Content

Every content decision should be traceable to a learning objective. If a screen doesn't help the learner achieve an objective, cut it or reframe it. The discipline of writing objectives before content is what separates a course from a guided tour of the documentation.

### Show, Don't Tell — Aggressively Visual

People's eyes glaze over text blocks. Follow these hard rules:

**Text limits:**
- Max **2–3 sentences** per text block. Fourth sentence → convert to a visual.
- Every screen must be **at least 50% visual** (diagrams, translation blocks, cards, animations, badges).

**Convert text to visuals:**
- A list of 3+ concepts → **cards with icons**
- A sequence of steps → **flow diagram** or **numbered step cards**
- "Component A interacts with Component B" → **animated data flow** or **architecture diagram**
- Dense spec language → **spec ↔ plain-English translation block**
- Comparing two approaches → **side-by-side columns**

**Visual breathing room:** generous spacing between elements; alternate full-width visuals with narrow text blocks for rhythm; every module has at least one hero visual.

### Spec ↔ Plain English Translations

Left panel: verbatim text from the documentation (as a styled blockquote — never modified, trimmed, or paraphrased). Right panel: a three-part annotation:

1. **What it means** — the plain translation
2. **Why it matters** — the practical consequence of getting this right or wrong
3. **Watch out for** — the gotcha, the edge case, the thing everyone gets wrong first

Never modify the spec text. If a passage is too long, *choose* a naturally self-contained excerpt. The learner should be able to open the original document and find the exact text they learned from.

### One Concept Per Screen

Each screen within a module teaches exactly one idea. If you need more space, add a screen — don't cram.

### Metaphors First — With Boundaries

Introduce every new concept with a metaphor. Then immediately ground it: *"In this spec, this looks like..."* Then add the boundary: *"This analogy breaks down when X, because in reality Y."*

The boundary is not optional. Every metaphor has a failure mode — learners who don't know where the metaphor ends form misconceptions that are harder to correct than if you'd used no metaphor at all.

**No recycled metaphors.** Never "restaurant" or "kitchen" more than once. Each concept deserves a metaphor that feels inevitable for that specific idea. The TTL is like a milk expiration date. An authoritative server is like a land registry — the definitive record, not a copy. RFC MUST/SHOULD/MAY is like legal language: MUST means the contract is void if you don't, SHOULD means you'd lose in court if you didn't without good reason, MAY means it's explicitly permitted.

### Cognitive Load Management

**Intrinsic load (complexity of the material itself):**
- **Pre-train components** before showing them working together. Teach what a resolver does in isolation before showing resolver → authoritative → resolver flows.
- **Segmentation**: break complex multi-step processes into sub-flows. Teach each sub-flow to completion before connecting them.
- **Worked examples → faded examples**: for complex processes, show a fully worked example first, then a partially worked one (with blanks), then ask the learner to complete or extend it. Never jump from example to quiz without a faded step.

**Extraneous load (complexity in the presentation):**
- Max 2–3 sentences per text block
- One concept per screen
- Visual over verbal everywhere possible
- No horizontal scrollbars — ever

### Formative Assessment Throughout

Don't save all assessment for the end of a module. Three formative patterns — use at least one per module:

**Prediction questions** (place before introducing a concept):
- *"Before we show you how TTL propagation works, what would you expect to happen if an intermediate cache extended a record's TTL? Keep your prediction in mind as you read on."*
- Creates a curiosity gap; activates prior knowledge; makes the correct answer more memorable when it arrives

**Mid-module knowledge checks** (1 question, embedded in content):
- Single inline question after a key concept, before moving to the next
- Low stakes — no score, just "you're tracking" vs "read that screen again"
- Immediately corrective: the feedback appears inline, not at the end

**Completion problems** (faded worked examples):
- Show a process with one or two steps left blank for the learner to fill in
- More challenging than a multiple-choice quiz; more supported than an open question
- See `references/interactive-elements.md` for the implementation pattern

### Spaced Retrieval — Cross-Module Callbacks

From Module 3 onward, every module begins or ends with a retrieval callback: a question or scenario that requires the learner to use a concept from an earlier module in a new context.

This is not a review question ("What did we say about X?"). It is a *transfer* question ("In Module 2 we learned that resolvers cache responses — given what you now know about authoritative servers, what would happen if an authoritative server returns a response with TTL 0 to a resolver that has already cached that record?").

The callback should feel like the material is building on itself, not testing whether the learner was paying attention.

### Summative Quizzes That Test Application

Placed at the end of each module. 3–5 questions. Every question must present a new situation the learner hasn't seen and ask them to *apply* what they learned — not recite it.

**Question hierarchy (use types 1–2 most):**
1. **"What would you do?" scenarios** — new situation, apply the knowledge
2. **Debugging scenarios** — something is broken, trace the cause
3. **Tradeoff evaluation** — two approaches, select and justify given criteria
4. **Tracing exercises** — follow the data/control flow through a new example

**Never quiz:** definitions, section numbers, verbatim text recall, anything answerable by scrolling up.

**Elaborative feedback on wrong answers:** don't just reveal the right answer. Explain *why the wrong answer is wrong* — what reasoning flaw it reflects, and what would have to be true for the wrong answer to be correct. This turns an incorrect attempt into a learning event.

Example of weak feedback: *"Not quite — the correct answer is B."*
Example of elaborative feedback: *"That would be correct if resolvers were allowed to extend TTLs from authoritative sources — but RFC 2181 explicitly forbids this to prevent cache poisoning. The reasoning the spec uses is that only the authoritative source knows how fresh a record actually is."*

**Quiz tone:** non-punitive, no score shown. The quiz is a thinking exercise, not a test.

### Glossary Tooltips — Every Term in Context

Every technical term with a precise meaning in this documentation gets a dashed-underline tooltip on first use in each module. The definition should explain what this term means *in this specific document*, not just the generic definition.

**Be extremely aggressive with tooltips:**
- Acronyms — ALWAYS on first use
- RFC normative language ("MUST," "SHOULD," "MAY," "RECOMMENDED," "OPTIONAL")
- Terms that look familiar but are used technically ("record," "field," "class," "type," "authority")
- Terms the primary learner's adjacent domain uses differently than this spec does

**Tooltip content structure:** plain-English definition (1–2 sentences) + a phrase on *how you'd use this term when giving instructions* — e.g., *"When asking an engineer about this, you'd say 'Is this a normative MUST or a SHOULD?' to find out how much flexibility there is in the implementation."*

**Cursor:** `cursor: pointer` (never `cursor: help`). **Positioning:** `position: fixed` appended to `document.body` to prevent clipping. See `references/interactive-elements.md`.

### Design Identity

Read `references/design-system.md` for the full token system. Non-negotiable principles:

- **Warm palette**: off-white backgrounds, warm grays — no cold whites or blues
- **Bold accent**: one confident color (vermillion, coral, teal — not purple gradients). Match to the subject matter's personality.
- **Distinctive typography**: Bricolage Grotesque for headings — never Inter, Roboto, or Arial
- **Generous whitespace**: modules breathe; max 3–4 short paragraphs per screen
- **Alternating backgrounds**: even/odd modules alternate warm tones for visual rhythm
- **Dark spec blocks**: dark background for spec-language excerpts — signals "official text"
- **Depth without harshness**: warm RGBA shadows only — never pure black

---

## Gotchas — Common Failure Points

### Teaching the Outline, Not the Understanding
The most common failure. Writing a course that mirrors the documentation's section structure rather than teaching the mental model. A section-by-section tour is not a course — it's a narrated table of contents. **Fix:** write learning objectives first. If your module structure maps 1:1 to the doc's section structure, you're following the outline, not the learning arc. Reorganize around *what the learner needs to understand first* to make everything else click.

### Objectives Written After Content
Writing content first, then adding objectives that describe what you already wrote. This is backwards and produces weak objectives. **Fix:** objectives must be written before content. If you catch yourself writing "understand" or "know," stop and rewrite with a Bloom's L3+ verb.

### Monolithic Learner Profile
Trying to serve multiple audiences (implementer AND decision-maker AND operator) in one course. The result serves none of them. **Fix:** name one primary learner in Phase 1A. Every content decision after that references this person.

### No Metaphor Boundary
A metaphor without a boundary teaches the concept and a misconception simultaneously. Learners extend metaphors past their valid range. **Fix:** every metaphor is followed immediately by one sentence explaining where it breaks down.

### Formative Assessment Missing
Quizzes only at module end means learners discover gaps after seeing all the content, not while learning it. **Fix:** include at least one prediction question, inline knowledge check, or completion problem per module, placed *before* the summative quiz.

### No Retrieval Callbacks
Each module is self-contained with no references back to earlier material. Learning fades quickly when concepts are only encountered once. **Fix:** from Module 3 onward, every module opens or closes with a retrieval callback that applies an earlier concept in a new context.

### No Synthesis Module
The course ends when the content ends. The learner's working memory never consolidates. **Fix:** always build the synthesis module — return to the opening scenario, show the assembled mental model, give a reference card.

### Weak Wrong-Answer Feedback
Feedback that just reveals the right answer without explaining why the wrong answer was wrong. **Fix:** for every distractor in a quiz, write what reasoning flaw it represents and what would have to be true for it to be correct.

### Prediction Question Single-Select Mismatch
Writing a prediction question whose reveal answer is "all of the above" (or any answer requiring multiple options) but using the default single-select (radio-style) interaction — where clicking any option clears the others. The learner is forced to pick one, then sees that every option was correct, making the interaction feel broken and dishonest.

**The root cause:** ask yourself *how many options should the learner have selected when they commit?* If the answer is more than one, single-select is wrong.

**Fix:** add `data-multiselect="true"` to the `prediction-block` div. This switches `selectPrediction()` to toggle-on-click (checkbox-style) rather than clear-all-then-set (radio-style). The commit button appears once at least one option is selected. Update the label to "Select all that apply" and rewrite the question stem to invite multiple selections ("Pick every option you think is plausible" rather than "Which one is most likely").

**Decision rule:**
- Use **single-select** (default): when exactly one option is most-correct. Stem: "Which one…" or "What would you expect…"
- Use **multi-select** (`data-multiselect="true"`): when the reveal is "all of these," "several of these," or any combination. Stem: "Select all that apply" / "Pick every option you think is plausible." Button text: "Lock in my answers →" (plural).

```html
<div class="prediction-block animate-in" id="pred-xyz" data-multiselect="true">
  <div class="prediction-header">
    <span aria-hidden="true">🤔</span>
    <span class="prediction-label">Before we continue — select all that apply</span>
  </div>
  <p class="prediction-question">
    <strong>Pick every option you think is plausible.</strong>
  </p>
  <div class="prediction-options">
    <button class="pred-option" onclick="selectPrediction(this,'pred-xyz')" data-value="a">Option A</button>
    <button class="pred-option" onclick="selectPrediction(this,'pred-xyz')" data-value="b">Option B</button>
  </div>
  <!-- Note: style="display:none" — shown by JS once ≥1 option is selected -->
  <button class="pred-commit" id="pred-xyz-btn" onclick="commitPrediction('pred-xyz')" style="display:none">Lock in my answers →</button>
  <div class="pred-reveal" id="pred-xyz-reveal"><!-- reveal --></div>
</div>
```

### Tooltip Clipping
Translation blocks use `overflow: hidden`. Tooltips using `position: absolute` inside the term element get clipped. **Fix:** tooltips must use `position: fixed` and be appended to `document.body`. Calculate position from `getBoundingClientRect()`.

### Accessibility Skipped
Interactive elements without keyboard operability, diagrams without alt text, color used as the only signal. **Fix:** apply the WCAG 2.1 AA baseline from Phase 3A before writing any interactive elements. Check: every control has an aria-label, every diagram has a description, every color signal has a text/icon pair.

### Walls of Text
Screens that look like formatted documentation. **Fix:** every screen must be at least 50% visual. Convert any list of 3+ items to cards; any sequence to a flow diagram; any spec excerpt to a translation block.

### Recycled Metaphors
Using "restaurant" or "kitchen" more than once. **Fix:** each concept gets its own inevitable metaphor. If you reach for the same metaphor twice, stop and find one that fits the specific concept organically.

### Scroll-Snap Mandatory
`scroll-snap-type: y mandatory` traps users inside long modules. **Fix:** always use `proximity`.

### Module Quality Degradation
Writing all modules in one pass causes later modules to become thin and rushed. **Fix:** build one module at a time. Verify each before starting the next.

### Scope Ignored
Trying to teach all the documentation, producing a course so long it's unusable. **Fix:** apply the 80/20 rule in Phase 1B. A course that covers 20% of the documentation well is worth more than one that covers 100% badly.

---

## Reference Files

Read these when you reach the relevant phase:

- **`references/firecrawl.md`** — Firecrawl MCP setup instructions and the full Phase 0 crawl procedure (mapping, URL filtering, batch scrape, credit usage). Read when the input is an `https://` URL, or when Firecrawl tools are unavailable and the user needs setup instructions.
- **`references/design-system.md`** — CSS custom properties, color palette with WCAG contrast ratios, typography scale, spacing, shadows, animations, accessibility notes, scrollbar styling. Read before writing any CSS.
- **`references/interactive-elements.md`** — Implementation patterns for every interactive element: spec↔plain-English translations, prediction questions, completion problems, mid-module knowledge checks, retrieval callbacks, scenario quizzes with elaborative feedback, decision tree navigators, state machine visualizers, data flow animations, architecture diagrams, drag-and-drop matching, callout boxes, pattern cards, flow diagrams, glossary tooltips. Read before building any interactive elements.
