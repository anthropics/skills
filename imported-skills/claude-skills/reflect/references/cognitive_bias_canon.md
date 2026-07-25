# Cognitive Bias Canon — 5 Biases + Recognition Cues

This reference answers exactly one decision: **which 5 cognitive biases does the reflect skill check for, and how does each manifest in conversation patterns?**

## The Core Frame

A reflection that doesn't check for cognitive bias is just a summary. The 5 biases below are the most operationally relevant for in-conversation reflection — each is detectable from specific conversational signals + correctable with a specific next move.

## The 5 Biases

| Bias | Definition | Conversation signal | Corrective |
|---|---|---|---|
| **Confirmation** | Seeking evidence that supports the working hypothesis; ignoring counter-evidence | Cited evidence one-sided; counter-evidence dismissed or absent | Run a disconfirming-evidence pass |
| **Sunk cost** | Continuing because of past investment, not future expected value | "We've already invested X" / "too far along to change" | Re-frame: ignore past investment, compute future value from current state |
| **Anchoring** | Stuck on first option mentioned; alternatives compared against anchor rather than evaluated independently | Multiple options discussed but always against the first one | Re-evaluate each option on its own merits, blind to ordering |
| **Complexity bias** | Adding features, steps, safeguards without specific justification for each | Each layer added is plausible but cumulatively bloated | Force "why this specifically, not without it?" per layer |
| **Recency bias** | Over-weighting last few turns; older important context being ignored | Recent details cited; original goal forgotten | Re-read from turn 1, not just the tail |

## 1. Confirmation Bias

Wason (1960) demonstrated that people systematically seek confirming evidence over disconfirming. In conversation, this manifests as:

- **Selective citation:** "X supports our hypothesis" without checking for counter-cases
- **Asymmetric scrutiny:** confirming evidence accepted; disconfirming evidence questioned
- **Strawmanning alternatives:** weak versions of opposing positions cited

### Recognition in conversation

Look for: 3+ supporting examples cited with no counter-examples; phrases like "everything we've found supports..."; competing hypotheses absent or only weakly framed.

### Corrective move

Ask: "What would falsify this? What's the strongest counter-case we haven't engaged with?" Run a disconfirming-evidence search. The dossier skill's ≥30% disconfirming rule is this discipline operationalized.

## 2. Sunk Cost Fallacy

Arkes & Blumer (1985) showed people irrationally continue based on prior investment. In conversation:

- **"We're far enough in to..."** signals sunk-cost reasoning
- **"After all that work..."** — past effort treated as locked-in value
- **Switching cost weighted higher than continuation cost** without specific calculation

### Recognition in conversation

Look for: explicit references to past investment without future-value calculation; resistance to pivoting that's framed by "we've already X" rather than "the alternative isn't better."

### Corrective move

Force this reframe: "If we were starting fresh today, with current information, would we still choose this path?" If no → pivot. Past investment is irrelevant to future decisions.

## 3. Anchoring

Tversky & Kahneman (1974) demonstrated that initial estimates persist even when irrelevant. In conversation:

- **First option becomes the default frame** even when better alternatives emerge
- **"Compared to X..."** when X was the first option — alternatives evaluated relative to anchor, not absolutely
- **Range-bound thinking** around the anchor's neighborhood

### Recognition in conversation

Look for: multiple options surfaced but discussion keeps circling back to the first; alternatives framed as "modifications of X" rather than fundamentally different approaches.

### Corrective move

"Forget the first option. If you saw these alternatives fresh, which would you pick on its merits?" The blind-comparison technique decouples evaluation from anchoring.

## 4. Complexity Bias

The opposite of Occam's razor — adding layers because they sound rigorous, not because each is justified. In conversation:

- **Each layer plausible in isolation** — but cumulative complexity exceeds problem complexity
- **Safeguards / wrappers / fallbacks** added speculatively without specific failure mode
- **"What about..." additions** without "would dropping this break anything?" check

### Recognition in conversation

Look for: a feature/layer/check added without naming the specific failure it prevents; cumulative architecture growing turn-over-turn without consolidation.

### Corrective move

Per layer: "What specific failure does this prevent? What goes wrong if we drop it?" If answer is vague, drop it. The Karpathy-coder discipline in this repo (`engineering/karpathy-coder/`) is this corrective formalized.

## 5. Recency Bias

The last N turns dominate working memory; turns 1-5 fade. In conversation:

- **Original goal forgotten** — work moved on, original constraint dropped
- **Recent micro-decisions cited** as if they were core principles
- **Strategic context** (set early) supplanted by tactical context (set late)

### Recognition in conversation

Look for: framing that references "what we've been working on" without referencing "what we were trying to accomplish"; absence of the original goal statement when justifying current direction.

### Corrective move

Re-read from turn 1. State the original goal explicitly. Compare current direction to original goal. This is the discipline that distinguishes the reflect skill from a local-context summary.

## When Multiple Biases Are Detected

In long conversations, 2-3 biases often surface together. Pattern:

- **Confirmation + sunk cost** = "we're invested AND it's working" (resist pivoting even when alternatives are stronger)
- **Anchoring + complexity** = "the first idea, with N safeguards" (over-engineered version of first option)
- **Recency + complexity** = recent additions become core; original simple goal forgotten

Surface each bias separately. Don't conflate. Each has a different corrective.

## Operational Checklist (Per Reflection)

For each of the 5 biases:

- [ ] Scan conversation for signal patterns
- [ ] If detected: name the bias, cite specific conversation evidence (with turn numbers if possible), suggest the corrective
- [ ] If not detected: state explicitly that you checked and didn't find it (so user knows you didn't skip the check)

The 5-bias check is the most under-performed step in casual reflection. Doing it carefully is what separates real reflection from rationalizing the current path.

## Citations (7 sources)

1. **Tversky, A. & Kahneman, D., "Judgment under Uncertainty: Heuristics and Biases" — *Science* 185(4157), 1974, pp. 1124-1131.** Foundational paper. Source for anchoring + several other biases the skill checks. The 50-year-old methodology still defines how we recognize these in real reasoning.

2. **Kahneman, D., *Thinking, Fast and Slow* (FSG, 2011).** Synthesis of decades of bias research. Source for the System-1-vs-System-2 framing that justifies reflection as a deliberate System-2 intervention against System-1 bias.

3. **Wason, P. C., "On the failure to eliminate hypotheses in a conceptual task" — *Quarterly Journal of Experimental Psychology* 12(3), 1960.** Foundational confirmation bias paper. The "2-4-6 task" showed people systematically test confirming hypotheses.

4. **Arkes, H. R. & Blumer, C., "The psychology of sunk cost" — *Organizational Behavior and Human Decision Processes* 35(1), 1985.** Empirical paper on sunk cost. Source for the "ignore past investment in future decisions" corrective.

5. **Russo, J. E. & Schoemaker, P. J. H., *Decision Traps* (Doubleday, 1989).** Practitioner-oriented synthesis of decision biases. Source for the "blind-comparison" technique that counters anchoring.

6. **Tetlock, P., *Superforecasting* (Crown, 2015).** Empirical evidence that "active open-mindedness" (Tetlock's term) is the #1 trait of accurate forecasters. The reflect skill's bias-check discipline is an operationalization of this trait.

7. **Karpathy, A., "Software 2.0" + various blog posts on engineering discipline.** Source for the complexity-bias corrective ("what specific failure does each layer prevent?"). The Karpathy-coder skill in this repo formalizes this.
