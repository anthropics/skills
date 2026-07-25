# Voice Calibration — Extracting Style from Sent-Email Samples

This reference answers exactly one decision: **why are real sent-email samples the highest-quality voice signal for inbox-triage's draft generation, and how does the skill extract usable patterns from them deterministically?**

Pair with `scripts/voice_sample_analyzer.py` for the deterministic extraction.

## The Core Claim

Users describe their own voice unreliably. They say "professional but warm" and their actual emails alternate between three sentences of formal hedging and "lol no" replies to colleagues. They say "I'm pretty casual" and their actual emails open with "I hope this email finds you well."

> **What users say about their voice ≠ what their voice actually is.**

Real sent emails resolve this gap. They show:

- Real opening phrases (not "I hope this email finds you well" if the user doesn't actually say that)
- Real sentence length (not "short" if the actual average is 3 paragraphs)
- Real sign-offs (not "thanks!" if the actual ratio is 80% "—Alex" and 20% no sign-off)
- Real register (the variation across recipient type that self-description misses)

## What S3.SAMPLES Asks For

> "Paste 3–5 real sent emails from your inbox."

3-5 is the operational sweet spot:

- **<3:** too few to detect patterns vs anomalies
- **3-5:** enough variance to detect baseline + adaptations
- **>5:** marginal signal, diminishing returns; takes longer to extract

The samples should span the user's typical email mix — at least one to a peer, one external, one transactional. If the user pastes 5 identical newsletters, ask for more variety.

## What `voice_sample_analyzer.py` Extracts

Deterministic stdlib analysis (no LLM):

1. **Opening phrases** — first 5-10 tokens of each sample's body. Pattern frequency.
2. **Sign-offs** — last 5-10 tokens of each sample. Pattern frequency.
3. **Sentence length distribution** — short (<10 words) / medium (10-25) / long (>25) ratio.
4. **Register markers** — counts of casual indicators ("lol", "yeah", "tbh", "btw") vs formal indicators ("I would like to", "please find", "kindly").
5. **Hedging frequency** — counts of softeners ("maybe", "I think", "perhaps", "just"). High hedging is a voice fingerprint.
6. **Personal pronouns** — "I" vs "we" frequency. Tells whether user writes as solo or representing a team.
7. **Punctuation patterns** — em-dash usage, exclamation marks, ellipses.

Output is a structured patterns block that goes into `email-patterns.md` under "Voice Patterns (Extracted from Samples)."

## How Self-Description (S3.Q1-Q6) Combines With Samples

Self-description and samples are **complementary**, not competing:

- **Self-description wins for:** hard rules (S3.Q6 — "never emojis"), forbidden tokens (S3.Q2 — "phrases I hate"), explicit sign-offs (S3.Q3 — what the user remembers using).
- **Samples win for:** baseline register, actual sentence length, opening phrases, register adaptation across recipient types.

In `email-patterns.md`, the two are combined: self-described preferences are stated as hard rules; sample-extracted patterns supplement as baseline behavior.

## When Samples Aren't Available

If the user refuses to paste samples (privacy, time, or just "I'd rather not"):

1. Honor the choice. Don't push back twice.
2. Use S3.Q1-Q6 self-description only.
3. Flag in `email-patterns.md`:

```markdown
## Voice Calibration Status

[calibration may need iteration — voice samples not collected during setup.
First few triage runs will likely produce drafts that need editing; the
system learns from your edits and overrides. Re-run inbox-setup with
samples when you're ready, OR triage will refine voice from your edit
patterns over 5+ runs.]
```

4. Inbox-triage will produce drafts in a more conservative default register (medium-formal, short-paragraph length). Drafts will need more editing on early runs.

## Common Anti-Patterns

### "I described my voice, that's enough"

Self-description has known blind spots (per the "Core Claim" above). Even high-self-awareness users overestimate their formality or underestimate their hedging frequency. Skip the samples and the first 10 triage runs produce drafts that "sound off" in a way users struggle to articulate.

### "I'll paste 5 emails that are similar"

5 emails to peers about the same project don't show register adaptation. The skill needs variance: one to a peer, one to a client/external, one transactional. If user pastes 5 similar emails, ask for one more from a different context.

### "I'll paste from my drafts folder"

Drafts may not represent voice the user actually sends — they may include rejected attempts. Ask for sent emails specifically.

### "I'll write 5 example emails for you"

Written-for-the-skill emails are self-description in disguise. Reject:

> "Examples written for me don't capture your actual voice — they capture how you describe your voice (which has known blind spots). Paste real sent emails, even short/boring ones. The mundane ones often signal voice better than carefully-crafted ones."

### "Forbidden tokens" extracted from samples instead of S3.Q2

Don't pull "forbidden tokens" from sample analysis — if a phrase appeared in a sent email, the user used it at some point. Forbidden tokens ONLY come from S3.Q2 (explicit "phrases I hate"). Voice extraction surfaces what the user DOES say, not what they DON'T.

## Operational Checklist (Per Setup Run)

- [ ] S3.Q1-Q6 asked one at a time with "why I'm asking"
- [ ] S3.SAMPLES asked AFTER Q1-Q6 (self-description first, samples second — samples calibrate the description, not replace it)
- [ ] 3-5 samples collected (or explicit user-skip + flag in patterns file)
- [ ] If collected: `scripts/voice_sample_analyzer.py` run; output incorporated into "Voice Patterns" subsection of patterns file
- [ ] Self-described hard rules + forbidden tokens preserved as authoritative
- [ ] Sample-extracted baseline preserved as descriptive (not authoritative)
- [ ] Calibration-status block included in patterns file (states whether samples were collected)

## Why This Reference Exists

The S3.SAMPLES step is the SINGLE most important question in the entire 25-31 question interview. Skipping it or doing it poorly compromises every subsequent triage run. This reference exists to make the discipline of "samples first, self-description second" explicit and operationally enforceable.

## Citations

Voice analysis canon:

1. **Brian Kernighan & Rob Pike, *The Practice of Programming* (Addison-Wesley, 1999)** — Chapter 1 on Style. The point that "names describe roles, not types" generalizes: a user's voice describes their habits, not their aspirations. Sample-based extraction captures habits.

2. **Steven Pinker, *The Sense of Style* (Viking, 2014)** — Chapter on register and the "Classic Style" trap. Self-described voice often defaults to Classic Style ideals that the user's actual voice doesn't match.

3. **Bryan Garner, *Garner's Modern English Usage* (5th ed., Oxford, 2022)** — Sections on register variation and register-adaptation across contexts. The justification for requiring sample variance (peer / external / transactional).

4. **Geoffrey Pullum, *The Cambridge Grammar of the English Language* (Cambridge, 2002), Chapter 12** — Register theory. Establishes that register is detectable from text features (sentence length, pronoun choice, hedging frequency) more reliably than from speaker self-report.

5. **Stylometric authorship attribution literature** — work by Patrick Juola, José Nilo G. Binongo, and the broader stylometry community. Establishes that text features (function-word frequency, punctuation patterns, sentence-length distribution) are robust voice signals. The features `voice_sample_analyzer.py` extracts are a subset of this canonical set.

6. **John Searle, *Speech Acts* (Cambridge, 1969)** — Performative theory. Useful framing for the "hard rules" (S3.Q6) discipline: hard rules are performatives the user commits to; voice is descriptive.

7. **Email-writing style guides at scale: *The Yahoo! Style Guide* (St. Martin's, 2010), *The Microsoft Manual of Style* (4th ed.).** Real-world style guides establish that register depends heavily on recipient + context, not on a single "professional voice." Justifies asking for sample variance.
