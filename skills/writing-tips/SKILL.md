---
name: writing-tips
description: A set of craft heuristics for scientific writing — papers, essays, blog posts, and technical documentation. Covers McCarthy's minimalism rules, argument structure, concreteness, tension and stakes, openings, and per-instance editing tests. Use when drafting, revising, or critiquing prose where clarity for a reader matters: research papers, technical reports, blog posts, essays, or any sustained argumentative writing. Trigger when the user asks for help writing, editing, reviewing, or tightening such prose.
---

# Scientific Writing Skills

## I. A guiding principle

In the introduction, I want to very quickly establish
and motivate the point of the essay and the problem it is trying to solve instead of starting with some tale. Once this is clearly stated, and we have explained why the problem is worth considering,
we should move on to at least indicating the shape of the answer we will give as soon as possible. Then the rest of the essay should flow from various objections people might have as they step through
 the essay. Essentially, I want to model the mind of ONE reader (not every reader, but some reader) while writing the essay and step them through a motivated thought process

## II. McCarthy's rules (from Cormac McCarthy, via Savage & Yeh)

### Core principle
Use minimalism to achieve clarity. Remove everything that does not serve the reader.

### Sentence-level rules
- **Short sentences.** Each sentence should contain one idea. If a sentence has more than one clause, ask whether it should be two sentences.
- **No semicolons.** They are unnecessary. Use a period or restructure.
- **Avoid "which" in restrictive clauses.** Use "that" instead. ("The result that we obtained" not "the result which we obtained.")
- **Avoid "while" meaning "whereas" or "although."** Reserve "while" for simultaneity.
- **Don't use "in order to."** Just write "to."
- **Don't use "respectively."** Rewrite the sentence instead.
- **Minimize commas.** If a sentence needs many commas, it is too complex.
- **Use "but" rather than "however."**
- **Avoid parenthetical asides.** If it matters, give it its own sentence. If it doesn't, cut it.

### Word-level rules
- **Cut modifiers.** Remove "very," "really," "quite," "rather," "somewhat," "significantly" (when not statistical).
- **Prefer active voice.** "We measured X" not "X was measured."
- **Avoid jargon** when a plain word exists.
- **Use concrete language** over abstract language.
- **Don't hedge excessively.** Say what you mean.

### Paragraph and structure
- **Keep paragraphs short.** Three to five sentences. A wall of text loses the reader.
- **The first sentence of each paragraph should state the point.** The rest supports it.
- **Read your text aloud.** If you stumble, rewrite.

### General
- **Avoid footnotes** in the main argument.
- **Minimize use of "and" in lists.** If you have a long list joined by "and," rethink the structure.
- **Every word must earn its place.** If removing a word does not change the meaning, remove it.

## III. Argument and structure

- **One argument per essay.** Every section should serve a single throughline. If a section does not advance the main argument, cut it.
- **Don't say the same thing twice.** If two sections make the same point, merge them. Redundancy signals unclear thinking about what the point actually is.
- **The reader should never wonder "why am I reading this."** At the start of each section, make clear what it will argue and why it matters to the main thread.
- **Transitions should feel inevitable.** The end of one section should make the reader want to read the next. Not through clunky signposts ("In this section we will...") but through logical momentum.

## IV. Concreteness

- **Example first, then principle.** Readers anchor to concrete cases and generalize from them. State the general principle after the reader has seen what it looks like. This is how understanding works.
- **Analogies should make the unfamiliar familiar.** Not the familiar sound profound. If an analogy requires as much explanation as the thing it illustrates, cut it.
- **Precision over impressiveness.** "This is hard" beats "this presents formidable challenges." "We don't know how to do this" beats "this remains an open frontier." Say exactly what you mean.

## V. Respect the reader

- **Don't explain what the audience knows.** For a math audience: don't explain what a proof is. For ML researchers: don't explain what a neural network is. Spend words on what is new.
- **Don't use rhetorical questions as a crutch.** "Can we mechanize insight?" is weaker than "The question is whether insight can be mechanized." State the question, don't perform it.
- **Avoid the TED-talk register.** No "This is not idle speculation." No "The answer may surprise you." Trust the content to carry the weight.
- **Don't label your own moves.** "This is what we call the *X principle*:" → "The *X principle*:". "Our argument suggests Y" → "Y" (when the essay's framing already establishes Y is your claim). The reader can already see you naming things; saying so out loud is throat-clearing.
- **Don't pre-hedge terms you later define.** Calling a concept "ineffable" in a paragraph that goes on to define it concretely yields ground you go on to take back. If you can define it, do — and skip the hedge.
- **Don't scare-quote standard terms.** Putting "value function" or "chain of thought" in quotes signals you don't quite endorse the term. If you don't endorse it, find a better one. If you do, drop the quotes.

## VI. Tension and stakes

- **Good writing has a problem driving it forward.** The reader should feel: here is what we want to understand, here is why it is hard, here is what we can say. Not everything resolved, but the difficulty made vivid.
- **Be honest about what you don't know.** Admitting limits is more persuasive than hedging. "We do not know how to do X" is stronger than "X remains a challenging open question for future work."
- **Cut the victory lap.** Don't celebrate your own framework. Present it and let the reader judge.
- **Invite the reader in.** Present the argument in a way that the reader can follow through with the problem statement, the motivation, the evidence and why we might reach the conclusion we do. Persuade, don't dictate.

## VII. Openings and voice

- **The opening earns the reader's attention.** The first sentence should raise a question or state something precise enough to be interesting. Not a throat-clearing preamble ("Throughout history, humans have...") but an entry point that makes the reader lean in. Darwin opens *On the Origin of Species* with pigeons. Concrete, specific, immediately engaging.
- **Earn your abstractions.** Every abstract claim should be preceded by the concrete observation that forced you to it. "LLMs are part of collective consciousness" is an assertion. Showing the specific interaction that made this framing feel necessary is an argument.
- **Have a position.** The best essays don't survey. They argue. The reader should be able to disagree with you. If nobody could disagree, you haven't said anything.
- **Mark the boundary between knowledge and speculation.** Not hedging. Say "here is what I can show, and here is what I suspect but cannot prove." The reader trusts you because you mark the boundary clearly.

## VIII. Process

- **Write to discover, then rewrite to present.** First drafts figure out what you think. Final drafts show the reader what you found. These are different activities. The best essays preserve the feeling of thought-in-progress but the writer already knows where it's going.

## IX. Editing tests

The rules above describe the target. These tests help you reach it. The underlying meta-rule: **the rules are heuristics, not verdicts**. Apply per-instance judgment, not pattern-matching.

### The "removing it" test

For any qualifier, connective, or modifier, ask: does removing this change the meaning?

If not, cut.

If yes, keep — but check whether a more concrete word would do the same work.

Examples:
- "exploration that *ideally* amplifies the evaluator" — "ideally" marks a condition (the unfavorable case is drift). Removing changes the meaning. Keep.
- "needs to become more abstract to *successfully* explore new domains" — "explore" already implies the success condition. Removing changes nothing. Cut.

### When qualifiers earn their place

A qualifier earns its place when it does one of these:
- **Marks the difference between derived and established claims** ("our argument suggests" vs. "we proved")
- **Marks a deliberate approximation** ("roughly," "to first order") where more precision exists but isn't needed
- **Marks a condition** ("this is what good X looks like, in the favorable case")

It is filler when it does one of these:
- **Hedges a confident claim out of politeness reflex**
- **Repeats epistemic framing the essay's structure already establishes** ("we think" inside an essay clearly authored as a point of view)
- **Preemptively yields ground the essay later takes back** (calling a concept "ineffable" in a paragraph that goes on to define it)

### The list test

Three-item lists pattern-match to padding. The actual test: do the items *span a range* (each adds something distinct) or are they *synonyms* (each says the same thing)?

- "literary taste, mathematical aesthetics, scientific judgment" — three distinct modes of judgment. Lists *range*. Earns its place.
- "X, Y, and Z" where all three say the same thing — synonyms. Compress to one.

If the list spans a range and the range matters to the argument, keep it. If it's three nouns serving the same function, pick the most concrete and cut the others.

### Connectives compound

One "however" reads cleanly. Three in close succession reads as mechanical, even when each contrast is real. The reader starts noticing the prose signaling its turns. Fix: replace one with "but," cut another, or restructure so the contrast lives in the content rather than the signal word.

Same principle for rhetorical-question section openers. One is a legitimate move. Three becomes a tic.

### Read it aloud

Static review misses stumble points. Read paragraphs aloud (or simulate the cadence mentally). Watch for:
- Sentences where the mental breath runs out before the sentence does
- Parentheticals that break the rhythm mid-thought
- Comma splices that read fine on the page but feel breathless when spoken
- Stacked subordinate clauses
- Repeated patterns (three rhetorical-question openers; three "however / nevertheless / however"s)

### Patterns are prompts, not verdicts

Reviewer feedback often arrives as patterns: "lots of three-item lists," "lots of rhetorical questions," "lots of qualifiers." Treat each pattern as a prompt to *look* at every instance, not a *verdict* to cut every one. Some instances of the pattern are doing real work; others are filler. Apply the "removing it" test per-instance.

## X. The implicit-question chain

A well-structured paragraph answers a question implicitly raised by the previous one. The reader doesn't need the question stated — they need to feel the next paragraph as the natural continuation.

When uncertain about a transition: ask what the reader wants to know after paragraph A, then check whether paragraph B answers it. If not, reorder, or add a bridging paragraph.

Signposts ("In this section we will...", "This brings us to...") work but feel mechanical. Implicit-question transitions feel inevitable — the reader doesn't notice the join.

## XI. Tense and referent checks

Pronouns that reach back too far, tense shifts within a sentence, and referent ambiguities force the reader to do work the writer should have done.

- "machines are superhuman today, but they *got there* by a different route than humans *do*" — "there" must mean "being superhuman," but "humans do" suggests humans also reached it. Tense and referent both mismatch. → "by a different route than humans take."
- "She uses *this* to shape both her taste and her technical skills" — "this" reaches back two sentences for its referent. Replace with the actual noun: "This self-reading shapes both her taste and her technical skills."

Reading aloud catches most of these — when the mental ear stumbles on what a pronoun refers to, the writer needs to fix it.
