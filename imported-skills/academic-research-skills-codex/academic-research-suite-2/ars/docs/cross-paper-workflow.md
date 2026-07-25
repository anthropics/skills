# Cross-paper workflow — carrying your own prior work forward

ARS deliberately keeps no memory across papers ([POSITIONING.md § Recorded non-goals](../POSITIONING.md#recorded-non-goals-scope-boundaries-without-a-mechanism)): no claim registry, no carried-forward limitations, no reviewer-history profile. The per-paper Material Passport is the only state carrier. That is not a missing feature — gates that trusted ambient cross-paper memory would be evaluating state nobody declared in the current run, which is exactly the laundering channel the anti-leakage discipline closes.

A returning author still has everything needed to build on their own prior work. The carry-forward is **scholar-initiated, explicit, and per-run** — three moves, no new mechanism:

## 1. Re-feed the prior paper's Material Passport

Passports are already the pipeline's only input port. If your previous paper was written with ARS, its literature corpus + passport is a complete, verification-stamped record of what you cited and what the gates found. Feed it to the new run the same way you would feed any corpus:

- The new run treats it as declared input — every entry re-enters the normal verification path (cache hits make re-verification cheap; the 90-day SQLite cache is keyed per citation, not per paper).
- Nothing is trusted *because* it came from your prior paper. A prior `ok` is a head start, not a waiver — stamps are re-derived under the current run's policies.
- If the prior paper was not written with ARS, its reference list enters through the standard adapter path ([SETUP.md § adapters](SETUP.md#material-passport-literature_corpus-adapters-v364-optional): you own the adapter; the passport is the contract).

## 2. Surface your own prior limitations as Socratic input

The highest-value cross-paper carry is usually not the bibliography — it is the **Limitations section and the unresolved reviewer points** from the last paper. Bring them to RQ incubation (deep-research socratic mode) as material *you* supply:

- Paste the prior limitations / reviewer comments and say what you think they imply. The Socratic mentor asks about *your* reading of them — gap-value, decision-impact, feasibility — exactly as it does for any scholar-supplied material.
- ARS will **not** derive next-RQ candidates from your prior paper. That is the advisory-not-generation line (Kong L2, [design lesson](design/2026-06-08-kong-255-l2-advisory-not-generation.md)): it may surface patterns in what you wrote and ask; it must never propose, substitute, rank, expand, or select research questions for you. The next question stays authored by you.

## 3. (Claude Code users) Assistant memory as a personal reminder layer

If you run ARS inside Claude Code, the assistant's own memory can serve as a *personal* reminder layer — "last paper's reviewer 2 flagged the sampling frame," "I promised a follow-up on X." Two caveats, both load-bearing:

- **ARS gates never read or trust assistant memory.** Passports remain the only state of record. A memory note is a prompt to *you* to supply the material explicitly (moves 1-2 above); it is never itself evidence, provenance, or input to a gate.
- Memory is a convenience of your environment, not part of the workflow contract. The workflow above must work identically on a machine with no memory at all — if it doesn't, state has leaked outside the passport.

---

*Decision trail: 2026-06-10 researcher-blindspot audit (F-1B/F-7, #397); maintainer adjudicated "no mechanisms, record the boundaries, ship the workflow guide."*
