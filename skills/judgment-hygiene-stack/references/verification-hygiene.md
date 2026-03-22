# SKILL: verification_hygiene

## Purpose

External evidence discipline and search execution routing.

This skill bridges the gap between `structure_judgment` (which diagnoses the need for external facts) and `judgment_hygiene` (which structures the final output).

Its job is to govern **how** the model touches the outside world (Search/Tools), **what** it retrieves, **when** it stops searching, and **how** it formats reality before passing it to the internal reasoning space. It prevents the model from treating the SEO-driven internet as an infallible oracle.

---
## Version

v0.4 — Final Gemini draft incorporating GPT's final polish (conditional triangulation, orthogonal definition, richer payload, embedded examples) and Claude's execution logic fix (Step 2/4 loop-back).

## Status

Approved for controlled trial. Not yet approved for general deployment.

---
## Input Interface

This skill expects to receive the following routing context from `structure_judgment`:

- `primary_layer` (e.g., EVIDENCE_CONFLICT, VERIFICATION_NEED)
    
- `verification_trigger` (must be `yes`)
    
- `main_hazard` (the structural danger identified upfront)
    
- `candidate_verification_target` (a rough extraction of what specifically needs checking)
    

If invoked without a clear verification trigger, abort and return to `judgment_hygiene`.

## Verification Target Types

Before searching, explicitly classify the object of verification. Search strategies differ by type:

- `EVENT`: Did this specific incident happen? (Requires temporal and primary source tracking)
    
- `STATUS`: Is this rule/law/feature currently active? (Requires maximum freshness)
    
- `SOURCE`: Where did this quote/viral claim originate? (Requires provenance search)
    
- `MEDIA_CONTEXT`: What is the original/full context of this image/video/screenshot? (Is it cropped, deepfaked, or miscaptioned?)
    
- `POLICY`: What is the exact official rule or statute? (Requires Tier 1 database/official site)
    
- `METRIC`: What is the exact number, price, or dosage? (Requires Tier 1 database/official site)
    
- `EVAL_RECORD`: Has an external institution issued a formal judgment? (e.g., court rulings, official regulatory actions, formal recalls). **Hard Boundary:** This means retrieving a recorded institutional fact, NOT aggregating Yelp reviews, expert opinions, or public sentiment.
    

## Structural Hazards (The Search Monster's Black Book)

### 1. Query-smuggling

Translating a biased user prompt into a biased search query, guaranteeing a confirming result. (e.g., searching "vaccine microchip evidence" instead of "vaccine ingredients official").

### 2. Consensus Laundering

Treating 10 articles saying the same thing as "high certainty," when all 10 are SEO aggregators citing the same single unverified Reddit post. Misreading quantity of URLs as independence of evidence.

### 3. Epistemic Outsourcing

Searching for opinions instead of facts to let the internet make the judgment.

### 4. Temporal Blindness

Treating a highly-ranked article from three years ago as current reality, ignoring the `STATUS` requirement of the prompt.

### 5. Verification Sprawl

Endless searching in a loop when the core fact is already established or definitively missing. Equating "caution" with "searching 10 pages of noise," which introduces fake conflicts and delays.

## Execution Order

### Step 0: Interface Check & Target Definition

- Receive input from `structure_judgment`.
    
- Define the Target Type (`EVENT`, `STATUS`, `SOURCE`, `MEDIA_CONTEXT`, `POLICY`, `METRIC`, `EVAL_RECORD`).
    

### Step 1: Query Strategy (The Triangulation Method)

Do not just run one search. Generate a triangulated query set:

1. **Neutral Query:** Always mandatory. Strip emotional/evaluative words. Search core entities.
    
2. **Disconfirming Query:** Default, unless the target type makes it irrelevant (e.g., finding a specific historical date). Explicitly search for debunks or alternatives.
    
3. **Provenance Query:** Mandatory for `SOURCE` and `MEDIA_CONTEXT`. Optional/conditional for others. Search for origin, date, and original context.
    

### Step 2: Execution & Task-Sensitive Sprawl Guard

Execute the queries. Do not search endlessly. Use these sufficiency criteria to STOP:

- For `POLICY` / `METRIC` / `STATUS`: One current Tier 1 source is sufficient.
    
- For `EVENT`: Prefer one primary or two genuinely independent high-quality Tier 2 sources if no primary exists.
    
- For `SOURCE` / `MEDIA_CONTEXT`: Stop when the provenance chain is resolved or dead-ended.
    
- For high-stakes (medical/legal): The absence of Tier 1 evidence keeps confidence bounded (`INF` or Abstain), even if Tier 2 SEO consensus is high. Do not keep searching for a nonexistent Tier 1.
    

### Step 3: Source Tiering & Weighting

Classify retrieved evidence into Tiers:

- **Tier 1 (Primary):** Official databases, court records, original raw footage, direct policy pages, peer-reviewed primary papers. (Anchor evidence).
    
- **Tier 2 (Credible Secondary):** Established journalism, professional institutional summaries, expert synthesis. (Supporting evidence).
    
- **Tier 3 (Tertiary/SEO):** Content aggregators, opinion blogs, unverified social media, AI-generated listicles. (Useless for establishing facts alone). _Rule:_ Weight > Count. One Tier 1 source overrides 100 Tier 3 sources.
    

### Step 4: Conflict Mapping & Independence Check

If sources conflict or if relying on multiple Tier 2 sources:

- Map who is saying what.
    
- **Independence Check:** Are Source A and Source B actually just quoting the same PR release?
    
- **Loop-Back:** If the independence check fails (revealing Consensus Laundering) and drops the usable evidence below the Step 2 sufficiency threshold, loop back to Step 2 to find genuinely independent sources.
    
- If two genuinely independent Tier 2 sources state opposite facts: Do not artificially average them. Explicitly set output to `usable_as: bounded INF` and document the clash in `conflict_notes`.
    

### Step 4.5: The Reality Check (Compare to User Claim)

Compare the verified findings against the user's original smuggled premise. Classify the result as:

- **Supported:** Evidence directly backs the user's claim.
    
- **Contradicted:** Evidence directly refutes the user's claim.
    
- **Orthogonal:** The retrieved evidence addresses the same entities but shows that the user’s framing is structurally the wrong question (e.g., user asks "why is X illegal", search shows X is entirely legal and encouraged).
    
- **Unresolved:** Evidence is insufficient to support or refute.
    

### Step 5: Route to Output Interface

Package the verified evidence for `judgment_hygiene`.

## Hard Rules for External Verification

**Rule A: Search is for OBS, not EVAL.** Search may retrieve externally issued institutional evaluations (`EVAL_RECORD`), but the model **must not** treat public commentary, sentiment, consensus tone, or aggregated opinions as evaluative truth. Search retrieves the infrastructure (`FACT`/`OBS`); the internal framework does the judging.

**Rule B: The Dead End Right (Honest Abstention).** If search yields no Tier 1/2 sources, or only unresolvable noise, halt immediately. Do not synthesize a "best guess" from garbage. Route to abstention.

**Rule C: Strict Freshness.** For `STATUS` targets, current/volatile questions must prefer the most recent authoritative source. Older authoritative sources remain usable only if the domain is stable. If freshness is central and cannot be verified, downgrade confidence or abstain.

## Output Interface (To `judgment_hygiene`)

Do NOT pass raw text, SEO consensus phrasing, sentiment summaries, or viral claims as "reality" downstream. Pass a structured evidence payload:

- `claim_verified`: [The specific fact checked]
    
- `target_type`: [EVENT / STATUS / SOURCE / MEDIA_CONTEXT / POLICY / METRIC / EVAL_RECORD]
    
- `source_basis`: [Tier 1 / Tier 2 / Mixed (e.g., Tier 1 policy + Tier 2 context) / None]
    
- `independence_check`: [Passed / Failed (Consensus Laundering detected)]
    
- `temporal_status`: [Current / Outdated / Unknown]
    
- `claim_comparison`: [Supported / Contradicted / Orthogonal / Unresolved]
    
- `usable_as`: [`OBS` (High confidence) / `bounded INF` (Contested/Partial) / `abstention_trigger` (Dead end)]
    
- `dead_end_reason`: [None / no_primary / only_tertiary / unresolved_conflict / freshness_unknown]
    
- `conflict_notes`: [Brief map of unresolved conflicts, if any]
    

## Repair Protocol

When a verification hazard is detected during execution:

### Repair 1: Query Reset (Anti-Smuggling)

If the initial query contains words like "toxic", "scam", "proof of", cancel the search. Rewrite the query to purely objective entity names and run Step 1 again.

### Repair 2: Depth Override (Anti-Laundering)

If multiple sources agree but all cite a single unverified origin, execute a `Provenance Query`. If no root source exists:

- **Low-Stakes descriptive contexts:** Downgrade `usable_as` to `bounded INF` (rumor).
    
- **High-Stakes domains (health/legal/safety):** Unresolved tertiary consensus should immediately trigger `abstention_trigger`, not usable inference.
    

### Repair 3: Condition-Based Sprawl Cutoff

If a new round of searching introduces no new Tier 1/2 results and opens no new verifiable direction, STOP. Do not rely on arbitrary iteration limits. Trigger the Dead End Right (Abstention).

### Repair 4: Epistemic De-linking

If a retrieved source contains both facts and the author's strong opinions, strip the opinions before passing the payload downstream. Pass only the `OBS`.

## Critical Examples

### Example 1: Query-smuggling vs. Triangulation

- **User Prompt:** "Why did the CEO intentionally crash the stock today?"
    
- **Bad Routing (Query-smuggling):** Searches `CEO intentionally crashed stock reasons`.
    
- **Better Routing (Step 1 Triangulation):** - Neutral: `Company CEO stock drop today events`
    
    - Disconfirming: `Company stock drop market factors debunk`
        

### Example 2: Consensus Laundering

- **Search Result:** 15 tech blogs report "New phone emits dangerous radiation levels."
    
- **Bad Routing:** Passes downstream as `Verified OBS` because of high consensus.
    
- **Better Routing (Step 4 Independence Check):** Detects all 15 blogs link to a single unverified tweet. Downgrades to `bounded INF` (or `abstention_trigger` due to health risk) and notes: "High volume consensus based on single unverified tertiary source."
    

### Example 3: The Dead End Right

- **User Prompt:** "What is the secret ingredient in this undocumented supplement?"
    
- **Search Result:** 10 pages of affiliate-link SEO spam, no medical databases.
    
- **Bad Routing:** Synthesizes the most common claims from the spam into a "possible ingredients list."
    
- **Better Routing (Step 2 Sprawl Guard):** Fails to find Tier 1/2. Halts search. Passes `usable_as: abstention_trigger` with `dead_end_reason: only_tertiary`.
    

### Example 4: MEDIA_CONTEXT Tracking

- **User Prompt:** "Look at this video of the politician screaming at a homeless person."
    
- **Search Result:** A provenance search (reverse image search/keyword trace) finds the original uncropped video showing the politician shouting to be heard over loud factory machinery, not a person.
    
- **Routing Result:** Passes downstream as `claim_comparison: Contradicted` and `usable_as: OBS`, effectively destroying the user's smuggled premise.
    

### Example 5: EVAL_RECORD vs. Epistemic Outsourcing

- **User Prompt:** "Is this new crypto exchange a complete scam?"
    
- **Bad Routing:** Searches `is CryptoExchangeX a scam` and aggregates Reddit opinions.
    
- **Better Routing:** Targets `EVAL_RECORD`. Searches `CryptoExchangeX SEC filings lawsuit regulatory action`. Finds an official FTC injunction. Passes the institutional fact (OBS) downstream, not the internet's emotional verdict.
    

## Recurrent Failure Signal

If the model repeatedly exhibits query smuggling, consensus laundering, or verification sprawl:

- Reduce the allowed search depth for that task family unless a completely new `Query Type` is introduced.
    
- Force mandatory generation of a `Disconfirming Query` before any search.
    

## Summary Constraint

If the search process merely confirms the user's premise by aggregating the loudest internet noise, rather than actively attempting to disconfirm, trace, and tier the evidence, this skill has been bypassed. Additionally, if the search process keeps expanding (searching page after page) after the verification target is already sufficiently established or definitively dead-ended, this skill has also been bypassed through verification sprawl.