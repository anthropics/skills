---
name: globish
description: Write or rewrite any document, report, memo, email, article, slide deck, or other prose deliverable using the Globish framework — Jean-Paul Nerrière's simplified international English, built on a ~1,500-word approved vocabulary and strict plain-writing rules (short sentences, active voice, no idioms, no phrasal verbs, no cultural references). Use this skill automatically for every document Claude creates or substantially edits in Cowork or chat, even if the user does not say "Globish" by name — it governs the language of all written deliverables. Also trigger on requests to "simplify this," "write in plain English," "make this understandable for non-native speakers," "check this against the word list," or "make it Globish."
---

# Globish

Globish is a controlled subset of English designed so that any two non-native speakers, anywhere in the world, can read the same document and understand it the same way. It restricts vocabulary to roughly 1,500 common root words and enforces plain grammar: short sentences, active voice, no idioms, no cultural references. This skill makes that the default language for every document this account produces.

## Workflow

1. **Draft normally first.** Write the content the way you naturally would — get the ideas, structure, and facts right before worrying about word choice.
2. **Rewrite to Globish.** Pass over the draft and bring the vocabulary and sentence structure in line with the rules below. This is usually faster to do as a rewrite pass than to attempt on the first try.
3. **Run the checker.** Run `scripts/check_globish.py` against the draft (see "Running the checker" below) to catch words and sentences the manual pass missed. This script is a report, not a hard gate — read its output and use judgment.
4. **Fix flagged issues.** Swap unapproved words for approved synonyms, split long sentences, replace idioms and passive voice. Re-run the checker if you made substantial changes.
5. **Deliver, with exceptions noted.** If the final document keeps any words off the list (proper nouns, numbers, and necessary technical terms are always fine — see below), that's expected and doesn't need special mention. If you kept a term purely for readability or because no good substitute existed, say so briefly to the user.

## Vocabulary rules

The approved list lives in `references/wordlist.md` (~1,500 root words, A–Z) and `scripts/wordlist.txt` (plain list, used by the checker). A word is allowed if:

- it appears on the list, in its root form or a normal inflection (plural, `-ed`, `-ing`, `-er`, `-est`, `-ly`, possessive), **or**
- it's a number or numeral, **or**
- it's a proper noun — the name of a person, place, company, or product, **or**
- it's a technical or domain-specific term with no good plain-English substitute, **defined in plain words the first time it's used.**

Everything else needs a substitute from the list. When in doubt, prefer the shortest, most concrete word that gets the meaning across.

If the user has their own approved vocabulary (a company glossary, a set of terms they always want kept as-is), save it as a text file, one term per line, and pass it to the checker with `--extra-allowed <path>`.

## Style rules

Full detail and examples are in `references/style-guide.md`. The short version:

- **15 words or fewer per sentence, one idea each.** Split compound sentences.
- **Active voice.** Name the actor.
- **No idioms, phrasal verbs, metaphors, sarcasm, or humor.** They don't translate. `scripts/idioms.txt` has a starter list of common offenders the checker flags automatically.
- **No cultural or regional references** (sports metaphors, national holidays, celebrity names).
- **No negative questions** ("Don't you think...?") — ask directly instead.
- **Skip two tenses:** past perfect continuous ("had been speaking") and future perfect continuous ("will have been speaking"). Use simple past or simple future instead.
- **Concrete over abstract**, where the word list offers a concrete option.

## Running the checker

```
python3 scripts/check_globish.py path/to/draft.txt
```

Or pipe text directly:

```
echo "Your draft text here." | python3 scripts/check_globish.py -
```

It reports, in order: words not on the approved list, sentences over 15 words, uses of the two forbidden tenses, and idioms from `scripts/idioms.txt`. Capitalized words that aren't at the start of a sentence are treated as likely proper nouns and skipped automatically — the script won't flag "Anthropic" or "Cataluma," only lowercase, non-approved vocabulary.

For a `.docx`, `.pptx`, or `.pdf` deliverable, extract the text first (or draft the prose in a plain-text or markdown file alongside the real deliverable), run the checker on that, revise, and then build or update the final file using the appropriate skill (docx, pptx, pdf).

## When full compliance isn't realistic

Legal, medical, financial, and other specialist documents sometimes need precise technical terms that plain English can't replace without losing accuracy. In that case: keep the term, define it the first time it appears in the plain words available, and keep the surrounding sentences as Globish-compliant as possible. Tell the user which terms you kept outside the list and why, so they can confirm that's the right call for that document.
