# Globish style rules

Globish is not just a shorter word list — it is also a plainer way of putting sentences together. A reader with limited English, working in their second or third language, should be able to read a Globish document once and get it right. Every rule below serves that one goal.

## 1. One idea per sentence, 15 words or fewer

Aim for sentences of 15 words or less. Each sentence should carry one idea. If a sentence needs "and," "but," "which," or a comma to hold two ideas together, split it into two sentences instead.

**Not Globish:** "The team missed the deadline because the vendor, who had promised delivery by Friday, sent the wrong parts, which forced us to reorder and wait another week."

**Globish:** "The team missed the deadline. The vendor promised delivery by Friday. The vendor sent the wrong parts. We had to reorder. We waited another week."

## 2. Active voice

Say who does what. Active voice names the actor; passive voice hides it and adds words.

**Not Globish:** "The report was reviewed by the finance team before it was sent to the board."

**Globish:** "The finance team reviewed the report. Then we sent it to the board."

## 3. No idioms, phrasal verbs, metaphors, or humor

Idioms ("move the needle," "touch base," "the ball is in your court") and business clichés don't translate. Phrasal verbs (verb + preposition combinations like "look into," "come up with," "get around to") are often the hardest part of English for a non-native reader, because the meaning has nothing to do with the individual words. Replace them with a single plain verb.

**Not Globish:** "Let's circle back once we've had a chance to dig into the numbers."

**Globish:** "We will talk again after we study the numbers."

Humor, sarcasm, and irony also don't survive translation — skip them in Globish writing.

## 4. No cultural or regional references

Skip references that assume shared background: sports metaphors ("home run," "slam dunk"), national holidays, regional foods, celebrity names, or idioms tied to one country's history. A reader in São Paulo, Seoul, and Stockholm should all understand the sentence the same way.

## 5. Avoid negative questions

Negative questions ("Don't you think we should wait?") are confusing to answer in a second language — a "yes" or "no" doesn't map cleanly onto agreement or disagreement. Ask directly instead: "Should we wait?"

## 6. Ten of the twelve English tenses — skip two

Globish uses ordinary tenses (simple present, simple past, simple future, present perfect, past perfect, future perfect, present continuous, past continuous, future continuous, and present perfect continuous) but drops two rare, hard-to-parse ones:

- **Past perfect continuous** — "He had been speaking." Use simple past instead: "He spoke for a long time before that."
- **Future perfect continuous** — "He will have been speaking." Use simple future instead: "By then, he will have spoken for an hour."

`scripts/check_globish.py` flags both patterns automatically.

## 7. Prefer concrete words over abstractions

Where the approved word list offers a concrete option, use it over an abstract one. "The machine stopped" beats "operational cessation occurred." Concrete nouns and verbs are easier to picture and easier to translate.

## 8. Numbers, names, and technical terms

Numerals, proper nouns (people, places, companies, products), and essential technical or domain terms are always allowed, even though they aren't on the word list — Globish was never meant to erase a company name or a chemical formula. Define any technical term the first time it appears, in plain words drawn from the approved list where possible.

## Quick self-check before delivering a document

1. Read it aloud. If a sentence needs a breath partway through, split it.
2. Underline every verb. Is it active? Rewrite any passive construction.
3. Search for "to," "up," "out," "off," "on," "into," "over" right after a verb — that's often a phrasal verb hiding a simpler word.
4. Run `scripts/check_globish.py` against the draft and review the flagged words and sentences.
