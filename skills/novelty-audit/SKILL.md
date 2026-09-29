---
name: novelty-audit
description: An adversarial verification protocol for novelty and whitespace claims. Use whenever a document, pitch, grant application, paper, or plan asserts that something is new, unexplored, "first", "nobody does this", or a market/research gap — before it is published or submitted. Also use when the user asks to check whether an idea already exists, find prior art, or map the whitespace around a topic. The deliverable is a per-claim verdict with citations, not new ideas. Do NOT use for generating ideas (that is creative-divergence's job), for general fact-checking of non-novelty claims, or for plagiarism and text-similarity checks — the audit adjudicates claims about what exists, not prose against its sources.
---

# Novelty Audit

Every novelty claim will eventually face an adversary whose entire job is one search: the grant reviewer, the referee, the investor's analyst, the patent examiner. This protocol runs the adversary's move first. Its premise is empirical: in literature-heavy domains, unaided priors misjudge what exists roughly as often as not — confidently seeing whitespace where there are literature reviews. The audit's primary product is prevented embarrassment; discovered whitespace is upside.

## Phase 1 — Extract the claims

List every explicit or implicit novelty claim in the input (a document, a pitch, or a stated idea). Implicit ones count: "we are the only", "unlike existing solutions", "there is no tool that", a gap statement in a paper, a differentiation slide. Number them. If the user supplied a topic rather than a document, ask what is being claimed as new, or derive the 2–4 strongest implied claims and confirm them in one line. State once in the deliverable: the audit verifies claims against the world's indexed record and assumes each claim is true of the user's own product or work — whether the described feature or capability actually exists is the user's side of the ledger, not the audit's.

## Phase 2 — Blind priors (before any search)

For each claim, state your own belief BEFORE searching: FULL (counterexamples exist), EMPTY (genuinely unclaimed), or UNKNOWN — with one line of reasoning and a confidence (low/med/high). **Write the priors into the output before issuing the first search** — priors held in reasoning and transcribed afterward are substantively honest but not mechanically auditable, and auditability is the point. This is the control: the audit's value is measured by how many verdicts differ from these priors. Never skip or backfill this step.

## Phase 3 — Adversarial sweep

For each claim, 1–3 queries designed to FIND the counterexample, not to confirm emptiness — search as the hostile reviewer would. Rules inherited from tested ancestors:

- Validate each query's aim: one numbered line per query, adjacent to that query — never an aggregate paragraph covering several, and the count of aim lines must equal the count of queries run. A query that returned adjacent marketing or a different actor's problem is MISFIRED and excluded.
- Match on mechanism, not vocabulary: a counterexample described in different words still kills the claim.
- Include at least one query in the claim's home language/region when the claim is regional.
- **Recall valve:** if the first round finds nothing against a claim, run one second round before issuing any verdict — mandatory for any claim heading toward SURVIVES or UNTRIAGED. The second round must CHANGE VOCABULARY FRAMES, not merely reword: if round one searched concept words (the mechanism, the category, the outcome), round two searches artifact words — vendor and product names, pricing-page language, "companies that", "platform for". For commercial claims, round two must include at least one software-directory or marketplace query (G2, Capterra, product directories, "site-style" category listings) — some occupants live in directories, not in search-phrase space, and three rounds of phrasing discipline cannot reach a cell that a different index holds. A synonym of a query that found nothing finds nothing; the strongest counterexample usually lives one frame — or one index — away.

## Phase 4 — Verdicts

Each claim gets exactly one verdict, with evidence:

- **KILLED** — a counterexample exists; cite it. Include the strongest one found, not the first.
- **SHARPENED** — the broad claim dies but a narrower edge survives (region, mechanism, combination, regulatory context). Rewrite the claim to its defensible form; cite what killed the broad version and what the sweep found nothing against.
- **UNTRIAGED** — nothing found, but absence is not yet evidence: state which of the three empty-cell causes remains unexcluded (unexplored / explored-and-died / invisible to the index: other language, practice-only, paywalled) and the single cheapest step that would triage it (a regional query, an expert to ask, a database to check).
- A claim only earns **SURVIVES** after a graveyard pass: search for failed attempts ("X failed", "X shut down", "X challenges") — a space can be empty because it is a graveyard, and claiming a graveyard as whitespace is the second-most embarrassing outcome available. The graveyard pass inherits the regional rule: a regional claim's graveyard must be searched in the claim's language and region — a global graveyard sweep cannot support "no failed local attempt".

Never promote absence to proof. "Not found" means "not the consensus of the indexed record", nothing more. Every KILLED and SHARPENED verdict must carry a citation; a verdict without evidence is a prior wearing a costume.

## Phase 5 — Deliverable

A claims table: claim → blind prior → evidence → verdict → rewritten claim (for SHARPENED) or replacement use (for KILLED). Then two short sections:

- **Salvage:** killed claims are not waste — a crowded cell is market/research validation. State how each killed claim converts ("the field is investing heavily in exactly this" beats false uniqueness in front of any reviewer).
- **Audit score:** how many verdicts differed from the blind priors, stated plainly. This is the honest measure of what the sweep added beyond the model's memory.

## Process exposure

Content-descriptive headings; no naming of this skill or its phases in the deliverable; if the user asks how the audit was done, explain fully and accurately. State the scope boundary when relevant: the audit reads the indexed record — it is strongest in literature-heavy domains and weakest where knowledge lives in practice, paywalls, or unindexed languages.
