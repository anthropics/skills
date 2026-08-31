# Cost Optimization - Cutting Spend per Completed Task

> **If you arrived via `/claude-api cost-optimize`:** this is the right file. Execute the steps below in order rather than summarizing the guide back to the user - presenting the profile, the ranked plan, and the findings IS part of the execution. Start with Step 0 (establish scope, quality bar, and baseline), and finish with Step 4's two deliverables: the cost profile and the changes.

API spend is optimized in units of **cost per completed task, not cost per token**. A model with a higher sticker price can be the cheaper option if it finishes the job in fewer turns, and a cheaper model that fails still bills its tokens, then the retry, then whatever the failure costs downstream. Every judgment below reads cost and quality together.

The levers divide into two kinds, and the order of the steps is load-bearing:

- **Free wins** - prompt caching, input-token hygiene (including a prompt audit), loop hygiene, output-token hygiene, batch processing - lower what you pay without lowering output quality. They go first, and caching stays on permanently.
- **Tradeoffs** - budgets, effort, model choice, multi-model architectures - exchange cost for intelligence. They go last, because each one changes what the model can do, and overshooting costs quality that the free wins never touch.

**Where this workflow sits**: the `prompt-audit` subcommand (`shared/prompt-audit.md`) audits the prompt surface (prompts, skills, tool descriptions) alone; this workflow is the holistic cost pass - request shape, caching, loop structure, output, batching, effort, model - and runs that audit as one sub-lever of input hygiene (§ 2.2) rather than restating its patterns; and once the project has an eval, the levers become a hillclimb - one change at a time against the eval, keep or revert (Step 3).

Measured expectations quoted below are snapshots of Anthropic's published runs (sources at the end). They are directional, not guarantees - the validation loop in Step 3 is what makes a number true for this project - and both sources are fetched live - the platform guide through `shared/live-sources.md`, the cookbook at its URL in the Sources section below: wherever a fetched page differs from this snapshot, the page wins.

---

## Step 0: Establish scope, quality bar, and baseline

**First, establish three things - from the request and the repository where they answer it, and from the user where they don't.** Unlike the prompt audit, this workflow is interactive by design: when context for a lever is missing, or a step would spend real money, work through it with the user rather than assuming. It is not expected to one-shot the audit. State all three at the top of the report (the baseline value itself may read "pending Step 1" at first).

1. **Scope.** If the request names files or directories, that is the scope. Otherwise it is every place the project calls the Claude API - request builders, agent loops, batch jobs. Note distinct traffic classes (an interactive path and a nightly job are different workloads even on one key): the profile, the ranking, and every validation later run per class, and "cost per task" means nothing blended across classes. **Also establish which platform** the code targets (first-party Anthropic API, Claude Platform on AWS, Bedrock, Vertex, or Foundry) - feature availability varies, and it filters which levers are even on the table.
2. **Quality bar.** Find the project's eval, test suite, or outcome checks for its LLM calls. If none exists, say so prominently in the report: without one, savings cannot be told apart from regressions. Do not stop - free wins are safe to propose regardless - but mark every tradeoff lever "needs an eval before applying", and ask the user what outcome check they can provide. An eval only validates the traffic class it covers: mark levers on uncovered paths the same way. If the only check is the user's own manual review, it gates free wins - it never clears a tradeoff. The full no-eval endgame - including a minimal eval recipe that unblocks tradeoffs - is in Step 3.
3. **Baseline cost per task.** The baseline is whatever honest number is cheapest to obtain, in this order:
   - **From history, free**: with Admin API access, pull Step 1's usage and cost reports forward and compute the baseline from them - the reports supply the dollars, but the per-task denominator must come from the user or the application's own logs; or roll up the application's own logged `usage` objects per task, not per request - four token counts, each at its own rate: regular input, cache writes (1.25x input for the 5-minute duration, 2x for 1-hour), cache reads (0.1x input), and output - multiplier structure as published on the pricing page; confirm it when you fetch the rates.
   - **From a baseline run, paid**: run the project's eval (or, with no eval, replay a representative sample of real requests) and roll up the same way. This spends real API money: state the expected cost - from Step 1's token estimates and live pricing, and "estimated - pending Step 1" is an acceptable first answer - **and get the user's approval before running it.** If the user declines the spend, estimate the baseline from the code and any bill figure they can read off the Console, label it an estimate, and continue.

   For current per-model rates, WebFetch the **Pricing** URL from `shared/live-sources.md` - prices change; do not quote remembered ones (if the pricing fetch fails, effective realized rates come from dividing cost-report amounts by the usage report's matching token counts - same model, same token type). For counting tokens in prompts and files, see `shared/token-counting.md` (`count_tokens` returns the count without running inference). Sanity-check an estimated baseline against any known monthly bill: divergence usually means multi-turn history growth the single-turn estimate missed.

## Step 1: Profile where the tokens go

The profile can be measured or estimated. Measure when the organization's access allows it; fall back to reading the code. Either way, the levers that pay are decided by the workload's shape, not by the list of what exists.

### Measure it - the Usage and Cost Admin API (preferred)

If the user has an **Admin API key** (`sk-ant-admin01-...` - a different key type from the standard API key; not available for individual accounts - creation and scopes are covered in the Admin API docs, reachable from the **Usage and Cost Admin API** URL in `shared/live-sources.md`), pull the real numbers instead of estimating. These are report reads, not model calls - they consume no tokens. Full parameters and response schemas: the **Usage and Cost Admin API** URL in `shared/live-sources.md`.

- **Token profile**: `GET /v1/organizations/usage_report/messages` with `group_by[]=model` and `bucket_width=1d` (the default page is 7 daily buckets - raise `limit`, up to 31; the `group_by` dimensions also include `api_key_id`, `workspace_id`, `service_tier`, and `context_window`, among others). Each result splits into exactly the quantities the levers below act on: `uncached_input_tokens`, `cache_read_input_tokens`, `cache_creation.ephemeral_5m_input_tokens` / `ephemeral_1h_input_tokens`, and `output_tokens`.
- **Dollar profile**: `GET /v1/organizations/cost_report` (daily granularity, USD as decimal strings in cents) with `group_by[]=description`; description-grouped results carry structured `model`, `cost_type`, `token_type`, and `service_tier` fields - `token_type` makes the cache split readable directly in dollars. Code execution appears under a `Code Execution Usage` description; Priority Tier costs are not included in this endpoint - track those through the usage endpoint's `service_tier` dimension.
- Data appears within about 5 minutes of a request completing; poll at most once per minute for sustained use.
- Caveats by platform: Claude Enterprise (claude.ai) organizations use the Analytics API instead, and the endpoints are not currently available on Claude Platform on AWS - there, ask the user to read the totals off the Console's Usage and Cost pages and relay them.

The measured profile answers directly: the real cache hit rate (`cache_read_input_tokens` against uncached input), how much traffic already rides the batch tier, the input/output balance, and where spend concentrates by model, key, and workspace. **Check that the measured footprint plausibly matches the audited code** (same models, a believable order of magnitude): the report covers the whole organization, and a key shared across projects blends their traffic - making per-project reads, including Step 3's post-cutover confirmation, unattributable. On a mismatch, reconcile against the code estimate, scope usage-report queries by `api_key_ids[]` / `workspace_ids[]` where the separation exists (the cost report takes neither filter - it segments only by workspace, via `group_by`), and recommend per-project keys or workspaces as a measurement prerequisite where it doesn't. Optimization effort follows the audited scope's spend, not the org blend.

### Estimate it from the code

Without Admin API access (no Admin key, a Claude Enterprise organization, or Claude Platform on AWS - whose feature availability `shared/claude-platform-on-aws.md` covers) - and even with it, for the structural facts no usage report can show - read the request-building code:

> **Per-model defaults, parameter support, and per-platform feature availability change across releases.** For any "what happens when `thinking`/`effort` is omitted", "does this model accept `effort`", "what levels does it support", or "is this feature available on Bedrock/Vertex/Foundry" question, read the answer from SKILL.md -> Thinking & Effort, `shared/models.md`, or `shared/platform-availability.md` (or the live Models API) - never assume, and never encode the answer in this guide.

- **Prefix**: how large are the system prompt and tool schemas, and is anything dynamic (timestamps, request IDs) interpolated into them?
- **Reference material**: is documentation or a manual inlined into every request?
- **Tools**: how many schema tokens, and does every request need every tool?
- **Loop**: how many turns deep, and do bulky tool results accumulate across them?
- **Media**: are images, PDFs, or large files entering the context at full size?
- **Output**: how long are visible responses, and what is `max_tokens` set to?
- **Model and effort**: which model, which effort, and was either ever swept against an eval? Look up what the model does when both are omitted (SKILL.md -> Thinking & Effort) - an unset default that runs thinking is a hidden output-token line item.
- **Caching**: are there `cache_control` breakpoints already, and what do `cache_read_input_tokens` / `cache_creation_input_tokens` show in practice?
- **Latency tolerance**: is a user waiting on every response, or can some work batch?

### Ask for the app's own usage logs first

Before ranking on estimates, **ask the user whether the application already logs `response.usage` per request** - and if so, to paste a representative day's worth. That turns cache hit rate, the input/output split, and thinking-token spend from guesses into measurements at zero API cost, and it decides which tier of the ranking table below applies. If the app doesn't log usage yet, note that adding it is itself a free-win diff (Step 3) and proceed on the code estimate.

**Estimating cache hit rate without usage data.** If the app logs request timestamps, simulate the TTL walk: sort timestamps, count a hit whenever the gap to the previous request is <= TTL (reads refresh the entry), and run it for each cache TTL the platform offers (see `shared/prompt-caching.md`) - the difference between durations is the longer-TTL lever's ceiling on the user's real traffic. If only aggregate volume is known, approximate with Poisson arrivals: hit rate ~ `1 - e^(-lambda·TTL)` where lambda is requests per second. Either beats comparing average gap to TTL, which ignores burstiness.

### Rank the levers

Before touching code, size each lever the profile makes applicable so the shortlist can be ordered. **How you quote the size depends on what data you have** - an estimate and a measurement must not look the same in the report:

| Data available | Quote each ceiling as |
|---|---|
| Admin API usage/cost report | **Dollar range**, labeled `measured` |
| App-side `usage` logs, or a user-reported bill total only | **% of current bill**, with dollars only as a parenthetical "(~ $Y at your reported $X/mo)" - the % is the claim; the $ is the user's own arithmetic |
| Neither (pure code read) | **Relative buckets** - "largest / medium / small", or an order-of-magnitude band - no specific figures |

**Before sizing, drop any lever the target platform doesn't support** (`shared/platform-availability.md` is the single source of truth - do not assume 1P availability carries to Bedrock, Vertex, Foundry, or Claude Platform on AWS). A lever that can't ship on the user's platform isn't worth ranking; list it under "skipped" with the availability reason instead.

Within whichever unit applies, size each lever from the measured (or estimated) spend components and the measured expectations quoted in Step 2 - for example:

- **Caching ceiling**: the spend on input that is shared and byte-stable across requests - the would-be prefix - re-billed at 0.1x. (0.025x on Claude Fable 5.1 - whether Claude Mythos 5.1 shares that rate is open at launch - so its cost per task sits at or under the Claude Fable 5 figures quoted below.) Blend the measured `uncached_input_tokens` with the code profile here: unique per-request payload can never cache, so on a workload that is mostly payload (or already well cached) this ceiling is honestly small. Sanity-bound the result against the published agent-loop range (a factor of 2.5 to 3.7 off at 81% to 90% hit rates).
- **Batch ceiling**: 50% of the spend on standard-tier traffic that no one is waiting on. The model-grouped profile cannot see that split - segment first: group by `service_tier` to find what already batches, use a finer `bucket_width` to spot scheduled spikes, and ask the user which traffic can wait.
- **Input-hygiene ceiling**: the share of input spend going to reference material, tool schemas, or oversized media that the § 2.2 levers would remove or defer.
- **Effort/model ceiling**: the published tradeoff curves applied to the biggest spend concentrations - carried as a range, since the quality cost is unknown until the eval runs.

Ceilings that claim the same tokens (caching an inlined document versus deleting it) are mutually exclusive: compute each ceiling unconditionally, rank, then deflate each for its overlap with the levers above it, so the shortlist can never sum past the bill.

Present the ranked shortlist with the profile evidence behind each number - labeled as ranked by savings ceiling, not application order (Step 2's § 2.x numbering decides the sequence) - and say where the list stops: a lever whose ceiling is a small fraction of the bill - or would not repay the approved runs and effort needed to validate it - does not earn an eval cycle, and most levers will not earn a place on any given workload (the "Workload shape -> lever" table near the end of this file is the map for matching profile to levers). On a small bill the honest shortlist may be empty: "nothing here is worth changing" is a successful finding, not a failure - report it plainly. Expected savings are planning numbers, not results - Step 3's measurements are the results.

## Step 2: Work the levers in order

Free wins may be applied directly when the request asked for edits (a bare subcommand invocation has not asked - propose). Tradeoff levers (2.6 onward) are always presented with their measured quality cost and applied only on the user's explicit acceptance - never trade accuracy for cost silently. And every run that exercises the model - the baseline, each lever's validation pass - spends real API money: get explicit approval before each one, with the expected cost, or once as a Step 3 measurement budget that covers them.

Pricing multipliers quoted below (cache read/write rates, batch discount) are current as of writing - confirm against the Pricing URL in `shared/live-sources.md` before computing any ceiling.

### 2.1 Prompt caching - first, and it stays on

Every turn of an agentic task resends the entire growing conversation - system prompt, tool definitions, every prior turn - so a 40-turn task sends its first turn 40 times and task cost grows with roughly the square of turn count. Caching does not stop the resending; it reprices it to 0.1x for everything already cached.

For design and placement - the prefix-match invariant, classifying inputs by stability, breakpoint patterns, the anti-pattern table - **read `shared/prompt-caching.md` and follow its workflow**; do not improvise `cache_control` markers. Points that matter specifically for cost:

- **Measured expectation**: the largest single lever on every model and benchmark Anthropic measured - it cut agent-loop cost by a factor of 2.5 to 3.7, at 81% to 90% hit rates; a small issue-triage agent's bill fell 83% from caching alone.
- **Explicit breakpoints when many independent conversations share a static prefix** (or prefix layers change at different rates). Automatic caching only amortizes within one conversation; in the cookbook's worked example, one explicit breakpoint on the static system prefix roughly halved cost per task across a queue of independent tasks. The robust shape for agent loops - one explicit breakpoint on the static prefix plus top-level automatic caching for the tail - and the cases where automatic alone is a pure surcharge are in `shared/prompt-caching.md` § Automatic vs explicit breakpoints.
- **Use the 1-hour cache duration when the loop waits on humans between turns.** It writes at 2x instead of 1.25x and pays for itself on the first prevented miss - a miss resends the whole prefix at full price and writes it again. Decide from the start-to-start gap between requests (generation time counts against the TTL) - the table in `shared/prompt-caching.md` § Choosing the TTL.
- **Audit for mid-task cache-breakers**: dynamic content above a breakpoint; changing `thinking` or `effort` between requests (always invalidates the messages cache, and on some models the tools+system cache too - `shared/prompt-caching.md` § Invalidation hierarchy); changing a task budget mid-task; every context-editing pass; switching models mid-conversation (caches are per-model).
- **Verify from usage, not from code review - and re-verify after every prompt-assembly change**: on a warmed-up loop, `cache_read_input_tokens` should dominate regular `input_tokens`, and `cache_creation_input_tokens` should be roughly one turn's worth, not the whole conversation. If it isn't, hunt for a cache-breaker with the healthy-loop signature and payload-diff method in `shared/prompt-caching.md` § Verifying cache hits - unless the workload's input is mostly unique per-request payload (which can never cache), or the misses are concurrent-batch artifacts (§ 2.5); neither is a breaker, and neither has a fix.
- **The cache probe, when there is no usage history to read**: a scratch script for the project's own stack that sends one representative request twice, byte-identical; prints all four usage meters (`input_tokens`, `cache_creation_input_tokens`, `cache_read_input_tokens`, `output_tokens`) for both; and exits non-zero if the second request's `cache_read_input_tokens` is zero. Ship it alongside the caching diff so the user can run the before/after themselves. It spends real tokens and may execute the project's tools - run it only under the standing approval rule, and point it at a scratch environment if the request's tools mutate state.

### 2.2 Input tokens - progressive disclosure

Send the model what the task needs, let it fetch the rest. Each sub-lever has a skip-when; the caveat at the end of this section governs all of them.

- **Large reference document in every prompt** -> move it behind a tool or skill so the model retrieves sections on demand. Skip when most calls consult most of it anyway - a document in the cached prefix is cheap - or when the eval shows misses on cases that hinge on rules the model now has to go looking for.
- **Tool recaps in the system prompt** -> delete them. Tool schemas already render into the request; prose restating them only inflates the prefix.
- **Many or heavy tool schemas** -> tool search with `defer_loading` on rarely-used tools, so definitions load only when needed. Pays once schemas run past roughly 10K tokens (MCP servers reach that fast); below that the search step is overhead. Measurement gotcha: the token-counting endpoint rejects server tools - read billed input off a `max_tokens: 1` request instead (a paid, if tiny, model call: it sits under the standing approval rule).
- **Images and PDFs at full resolution** -> pre-downscale to what the task needs. Vision inputs are tokenized by pixel area at roughly one token per 28×28 patch, so cost scales with resolution, not information content; 1280×720 is a safe default that caps an image near 1,200 tokens (current formula - verify via the Vision docs in `shared/live-sources.md`).
- **Large tables and artifacts inlined** -> Files API plus code execution: mount the file, let the model compute in the sandbox, and only the answer enters context. Skip when there is nothing to extract or compute - the sandbox round-trip only adds tokens (and sandbox container time bills hourly beyond a free allowance).
- **Fetched web pages** -> dynamic filtering in the web fetch tool keeps boilerplate out of the context.
- **Chained tool calls whose intermediates don't matter** -> programmatic tool calling runs the calls from code so only the filtered result enters context; its documentation reports 24% fewer input tokens on agentic search benchmarks, with a higher score.
- **Broad data-dump tools** -> prefer narrow accessors (`get_policy(claim_id)` over `get_all_policies()`), and give list tools `limit`/`fields`/`date_range` parameters.
- **Unbounded user-supplied input** -> the token-counting endpoint as an ingestion gate (`shared/token-counting.md`): count first, then truncate, summarize, or route oversize payloads to the Files API.
- **The prompt text itself** -> run the `prompt-audit` subcommand (`shared/prompt-audit.md`) as part of this step; its pattern tables are the reference for dated prompt text (this guide deliberately does not restate them), and its report and proposed diff fold into this workflow's deliverables. Skip when the prompt surface is small and recently audited. Prompts written for an older model make the current one over-work: on a support-desk evaluation, prompts written for Claude Opus 4.8 cost 36% more per ticket on Claude Opus 5 for no change in accuracy; audited, the same prompts were 14% cheaper than unaudited and more accurate (97% of tickets, up from 92%). On the Claude Sonnet 4.6 to Claude Sonnet 5 migration the audit took 14% off at the same accuracy.

**Caveat for the whole section**: a smaller prefix is not automatically a cheaper task. Deferring context means the model may spend discovery turns fetching what it previously read inline. Validate against the eval - on the cookbook's workload, wrapping the manual in a tool matched the explicit-breakpoint config on cost and gave back accuracy.

### 2.3 Agent-loop hygiene - keep long loops from compounding

Only relevant when the profile shows deep loops with bulky accumulating results; short loops never trigger these and the added machinery is pure overhead.

- **Context editing** (clearing old tool uses or thinking) **is a context-window tool, not a savings lever.** Every clearing pass rewrites the cached conversation, which works against prompt caching - in the run measured for the platform docs, context editing cost more than it saved. Use it to make room in the window; set the trigger high enough that clears stay infrequent, and clear in a few large batches rather than every turn.
- **Compaction** (the server-side summarize-and-continue edit) needs sessions long enough to reach its trigger; where it fired once on a long triage run it cut the bill a further 38%. Steer it with its `instructions` string so task-critical state survives the summary.
- **Client-side pruning at natural boundaries**: collapse bulky tool results to one-line extracts when a work phase completes, keeping the message array byte-identical between prunes so each prune is one cold cache miss rather than a new miss every turn.
- **Subagents for self-contained bulky steps**: a nested loop absorbs its own heavy tool results and hands back one line, optionally on a cheaper model. Skip when the deciding model needs the intermediate context to judge well - and note the subagent starts a fresh prefix with no cache shared with the parent.

### 2.4 Output tokens

- **`max_tokens` is a backstop, not a tuning knob.** The model never sees it; hitting it cuts the response off mid-thought with `stop_reason: "max_tokens"`. In Anthropic's coding runs a 16,384-token cap ended 15% of Claude Opus 5's attempts and a third of Claude Fable 5's, none of them solved - capped runs spent less per attempt and bought proportionally fewer solves, so cost per solved task didn't improve. Set it to 64,000 for agentic work (128,000 at `xhigh` or `max` effort), stream responses that large, and treat `stop_reason: max_tokens` as a failed attempt rather than retrying at the same cap.
- **To shorten visible responses**, specify the exact output shape in the prompt, ideally with an example. To shorten reasoning, that is the effort parameter (§ 2.6) - not `max_tokens`.
- **Stop sequences as content-aware early exits**: register a sentinel the model emits when it cannot proceed (for example `<CANNOT_REVIEW>`), so it stops instead of spending tokens explaining.

### 2.5 Batch processing

50% off **every token in the request, including cache reads and writes** - the discounts stack. The second-largest free lever after caching for unattended agent work - evaluation runs, backfills, scheduled jobs.

- Results arrive asynchronously within 24 hours; that window is an expiry, not an SLA. Keep user-facing work synchronous.
- Batch requests are single-shot - no mid-batch tool loop. A tool loop can sometimes be flattened into one batchable request by pre-fetching its inputs up front; in the cookbook's worked example that ran at roughly half the interactive config's cost, but it is an architecture decision, not a parameter - it changes how the model reasons (the flattened run held its pass rate less firmly), and cache hits inside a concurrent batch are best-effort.
- Not available for Managed Agents sessions (current mechanics and availability: the **Batch Processing** URL in `shared/live-sources.md`).

### 2.6 Effort and budgets - the first tradeoffs

From here down, every lever trades capability for cost. Sweep on the eval, one change at a time.

- **Sweep effort before touching the model** (on models that expose an effort parameter - check `shared/models.md` or the **Effort Parameter** URL in `shared/live-sources.md`). Effort scales thinking and tool-call depth without changing the model. Test each level in a separate session - changing effort mid-session invalidates the cache and distorts the comparison. Sweep mechanics that keep the comparison honest:
  - Cells are byte-identical except `output_config.effort`; same model throughout. Complete every sample request at one setting before starting the next, in a stable order, so cache reads are comparable across settings - and if the cache meters still differ materially between settings, say so and weight the read toward output-side cost.
  - Include a hard case the user knows about: curves are flattest on easy tasks, and the hard tail is where higher effort earns its cost.
  - **Side-effect gate**: if replaying a sample request executes tools that mutate real state, point the replay at a scratch environment or stub those tools first; a sweep is never worth a production mutation. If that isn't possible, sweep only the requests that are safe to replay and say so.
  - Read the curve as flat (the lower setting does this workload's work), steep (the higher setting is earning its cost - now a measured number rather than a fear), or mixed (name which tasks flipped - those are the candidates for the re-run-failures policy below). Differences of a task or two of pass rate, or cents of mean cost, are within noise on single runs; the remedy is repeat trials at the settings in contention, offered with their cost.
  - The curve is per-workload *and* per-model. Keep the sample and the outcome check where the report says they live, and re-sweep after a model migration, a major prompt change, or a workload shift.

  What to expect by workload shape:
  - Research and knowledge work: nearly flat curves - in Anthropic's runs (all with Claude Fable 5), `low` gave up 1 to 3 points for a third to a half off cost per task; `medium` matched the default's accuracy at 70% to 85% of its cost; the default bought nothing measurable over `medium` on any of the four benchmarks measured. Lower effort is also faster (4.5 versus 7.9 minutes per problem on one research benchmark).
  - Long-horizon coding: a real tradeoff - Claude Opus 5 gave up about 2 points at `medium` for half the cost, and about 8 points at `low` for a quarter of it.
  - Reasoning-ceiling work (deep multi-subtopic research): every effort step bought about 2.4 rubric points - no free cut on that curve.
- **Re-run failures at higher effort** - when the workload has a usable failure signal (tests, a checker, a validator). Run everything at `low` and re-run failures at the default: in Anthropic's coding runs, about 93% passed for about $0.70 per task, against 91.7% for $1.39 running everything at the default - the same pass rate for half the cost, counting the failed cheap attempts. Starting at `medium` solved about 94% for about $0.95. Use this for the saving, not the lift, and price in the checker and the doubled wall-clock on failures.
- **Task budgets** (the model sees the budget and paces itself - this is the budget control that saves money): set from the loop's 90th-percentile token usage, then tighten. The budget is advisory - it steers the model rather than stopping it - so verify adherence on the workload. Measured on coding: a generous budget gave up about 2.7 points of pass rate for an 18% saving; the tightest allowed budget gave up 4.4 points for 47%. Budgets below the 20,000-token floor are rejected; very tight budgets can produce refusal-like behavior; set the budget once on the first request - a mid-task change invalidates the cache. Check model availability before wiring it in (beta, and not available on every current model) - parameter shape, the streaming requirement, and supported models are in this skill's SKILL.md -> Task Budgets (Quick Reference) and `shared/model-migration.md` -> Task Budgets.
- **Backstops that don't save per-task money but cap the damage**: a Managed Agents session budget is a hard dollar stop; a workspace spend limit is the final backstop on the whole workspace.

### 2.7 Model selection - last, deliberately

Model choice constrains the intelligence ceiling, which is why it comes after every lever that doesn't.

- **Price candidates in cost per completed task on your own traffic**, including the larger model at reduced effort - per-token price lists do not predict the ranking. In Anthropic's runs, Claude Fable 5 at `low` effort beat Claude Sonnet 5 on a deep-research benchmark while costing about 10% less per task; on a coding subset both models largely saturate, Claude Opus 5 matched Claude Fable 5 (91.7% versus 91.3%) at about 60% of its cost. For most agent workloads, start with Claude Opus 5. At the other end, Claude Haiku 4.5 answered knowledge questions at about a tenth of Claude Opus 5's cost per question at 63% accuracy versus 92% - it fits high-volume work with checkable outputs, not long agentic loops.
- **Price the tail, not the median.** Compare models on the hardest tenth of the workload: on the typical task every model looks similar and the cheapest looks best, but the bill is decided by the tasks the cheap model fails - and the tail is where the money goes even when nothing fails (on one 20-problem research run, two problems carried 43% of the spend).
- **The stepping-down method**: sweep effort on the current model first; if `low` passes the eval, drop one model tier, **confirm which parameters and effort levels the target tier supports** (SKILL.md -> Thinking & Effort), reset effort to that tier's default - not a hardcoded level; the default and the supported range vary by model - and re-sweep down from there (on a tier without `effort` support, evaluate at its single default only). One notch at a time, against the eval - and when there is no cheaper tier, the lever is exhausted; say so rather than inventing a step. Current model lineup and discovery: `shared/models.md`; for model-swap mechanics and per-target breaking changes, the `migrate` subcommand (`shared/model-migration.md`).
- **Two models can beat one, in exactly two measured shapes** - both are architecture changes; validate like one:
  - **Advisor** (a cheaper executor runs the loop and consults a frontier model on hard decisions): pays when the capability gap between the two models is wide and the executor actually consults. The consult rate is the fragile variable - lowering effort can drop a pairing from consulting on most tasks to almost none, and then it scores below the executor alone - and gating the consult well requires a cheap signal; asking the executor to recognize the hard cases itself demands the very judgment it's missing. Benchmark first: on Anthropic's coding benchmark the flagship pairing was the most accurate configuration measured but sat within noise of the frontier model alone at `medium` effort, at about the same cost - sweep effort and price the stronger model alone before adding the advisor.
  - **Orchestrator** (a frontier model plans and delegates bulk work to cheaper workers): buys something only when there is bulk to hand off - many independent pieces, ideally too many for one context window. On work larger than any context window it cost 55% less than the frontier model solo at every effort setting (3 to 7 points below its best score); on routine search work it paid as tail insurance (about half the average cost, a third at the 90th percentile) but reversed on the harder full set. When the work is one dependent chain, or fits in a single context, the orchestrator pays for a plan, a handoff, and a merge that a single model gets for free - in every such case measured, the coordinator's model alone at lower effort came out ahead.

## Step 3: Apply, measure, keep or revert - one lever at a time

- Work down the ranked shortlist to decide which levers earn a diff - but **apply shortlisted levers in the § 2 order** (free wins -> effort/budgets -> model), not in savings-rank order: the ranking decides inclusion and where the eval budget goes; the § 2.x numbering decides sequence. Each lever that earns a place becomes **its own diff** (one lever per diff, so a revert is clean and effects attribute), applied and then measured: re-run the eval covering that lever's traffic class, and read pass rate and cost per task together against the previous kept configuration (the baseline for the first lever only). A lever that saves money and gives back accuracy is not an optimization - revert it and record why. A lever touching a path no eval covers cannot be validated by the eval you have: a free win there is measured on cost only, and said so; a tradeoff there stays an unapplied proposal (Step 0.2's marking rule).
- **Ask for the measurement budget once, not per run.** Present the validation plan with its total expected runs and cost - an effort sweep is several configurations at several trials each - and get it approved as a budget; within an approved budget, individual runs need no fresh approval. A shadow-run on live traffic roughly doubles production spend while it runs: it is its own approval.
- **Never keep or revert on a one-case swing.** Repeat trials within the approved budget until the decision clears the noise. The published bar - around fifty cases and at least five trials per configuration - is the standard for the production cutover; a smaller project eval is acceptable for per-lever decisions when trials are repeated. And validating a caching diff needs a warm cache: run the sample sequentially and measure from the second request on, or the 1.25x writes dominate and the free win reads as a regression.
- **When the user can provide no outcome check at all**: free wins become cost-only-measured diffs (or proposals, if no spend is approved), tradeoffs stay unapplied proposals carrying the published expectations, and offer a manual before/after spot-check of a handful of real answers - the user's review gates free wins, never a tradeoff. For an effort sweep specifically, a cost-only run is still worth offering: the same matrix with no pass-rate column, reporting per task the outputs at each setting laid side by side - exactly what the user needs in front of them to judge quality themselves. State plainly in the report which mode ran, and do not invent a grader to fill the gap. If the application doesn't log usage, adding `response.usage` logging is itself a free-win diff, and it is the measurement channel for everything after it when there is no Admin API key.
- **Minimal eval recipe** - the cheapest thing that clears a tradeoff lever, so "needs an eval" is a next step rather than a dead end. Offer to build it with the user:
  - **Inputs**: a fixed set of ~20-30 real requests pulled from production logs or written by the user - enough for per-lever keep/revert decisions (the ~50-case bar above is for the final production cutover). Freeze them; every config runs the identical set.
  - **Judgment per output**: whichever is cheapest for the workload - golden answers to diff against, a short rubric the user scores each output on, or an automated checker (tests pass, JSON validates, required fields present). A model-graded judge is acceptable when nothing cheaper exists, but it is itself an approved API spend.
  - **Runner**: a script that runs the frozen inputs through one config, records each output plus `response.usage`, and reports pass rate and cost per task. Each config is one invocation; the sweep is a loop over configs.
  - **Cost and approval**: estimate it (inputs × configs × baseline cost per task) and get the user's go-ahead before running - this is real API spend under the standing approval rule.
- Keep-or-revert is decided locally, on the eval evidence. Shadow-run the winning configuration on live traffic before cutover, keep the eval running after it, and confirm the savings in the usage and cost reports **after** cutover - only where the traffic is attributable (Step 1's shared-key caveat applies to the confirmation read too).
- Expect most levers not to fit any given workload. On the cookbook's worked example, most didn't earn a place - tool schemas too small for tool search, loops too short for editing or compaction, no numeric work for code execution - and the levers that came closest on cost each gave back a correct answer. The profile from Step 1 exists so optimization isn't blind.
- Plot configurations as score versus cost per task and take the Pareto frontier - that is what the cutover decision reads from.

## Workload shape -> lever

Adapted from the cookbook's takeaways table, for mapping a profile to levers (row 1's watch-out is extended):

| Where the cost is | Reach for | Skip it or watch out when |
|---|---|---|
| Same system prompt and tools re-billed on every call | Prompt caching with auto first, then an explicit breakpoint on the static prefix when many independent conversations share it or prefix layers change at different rates, and 1-hour TTL if calls are more than five minutes apart | Anything dynamic sits above the breakpoint - move that content into the user turn. And a cache that already reads well needs nothing: concurrent-batch misses (§ 2.5) aren't breakers, and a 1-hour TTL doesn't reach calls that are hours apart |
| Large reference document in every prompt | Move it behind a tool or skill | Each call needs most of the document rather than a section, or the eval shows misses on cases that hinge on rules the model has to go looking for |
| Many or heavy tool schemas | Tool search with `defer_loading` | Under roughly 10K schema tokens, where the search step is overhead |
| Images, PDFs, or large files in context | Downscale images to what the task needs, and use the Files API plus code execution for tables and PDFs | There is nothing to extract or compute so the sandbox only adds tokens |
| Unbounded user-supplied input | Token counting as an ingestion gate | |
| Bulky results piling up across a long loop | Context editing or compaction server-side, or a client-side prune at natural boundaries | Loops are short or the cleared content is still needed, and note that every edit breaks the cache from that point |
| One self-contained step with bulky intermediates | Subagent, optionally on a cheaper model | The deciding model needs that intermediate context to judge well |
| Long visible responses | Specify the output shape with an example, with `max_tokens` as a backstop and a stop-sequence sentinel for early exits | |
| Thinking and tool calls dominate, and the eval has headroom | Lower `effort` first, then drop a model tier and re-sweep effort | Always a direct capability trade, so step down one notch at a time against the eval |
| Mostly routine cases with a few hard ones | Advisor tool on a cheaper driver | There is no cheap signal to gate the consult, leaving the driver to spot hard cases itself |
| No one is waiting on the response | Batch API, flattening a tool loop into one request by pre-fetching its inputs if you have to | A user is waiting, or when flattening changes how the model reasons |

## Step 4: Deliverables

1. **The cost profile and plan**: the Step 0 assumptions (scope, quality bar, baseline), the Step 1 token profile, and the levers chosen with the measured expectation each one carries - plus the levers deliberately skipped and why, so the next person doesn't re-litigate them. Label the shortlist table as ranked by savings ceiling, not application order, so it can't be misread as the diff sequence.
2. **The changes**: one diff per lever so effects attribute - applied and measured (expected versus measured cost per task, pass rate held or not) where the user approved the runs; left as proposals carrying their expected savings and published quality cost where they didn't, or where a tradeoff lever still needs an eval. When nothing cleared the ranking floor, this deliverable is "no changes recommended" - a successful outcome; say it plainly rather than manufacturing a lever.

**Report skeleton** (section order and required columns - keep the rest flexible):

- **Scope / quality bar / baseline / platform** (Step 0 assumptions)
- **Token profile** (Step 1)
- **Ranked shortlist** - table columns: `Lever | Type (free win / tradeoff) | Savings ceiling | Data source (measured / usage logs / code estimate)`. Ceiling is in the unit tier the data supports (Step 1 -> Rank the levers). Caption the table "ranked by savings ceiling, not application order."
- **Proposed changes** - one diff per lever, numbered in § 2 application order (free wins -> effort/budgets -> model), each tagged *applied and measured* / *proposed* / *needs an eval*
- **Levers skipped** and why (including any dropped for platform availability)
- **Next step / approvals needed** - measurement budget ask, eval prerequisite, or "no changes recommended"

## Sources and live references

The measured results above come from two published Anthropic sources (and the Admin API facts in Step 1 from a third); fetch them when the user needs the full write-ups, charts, or current numbers:

- The platform guide **Optimizing for cost and intelligence** - WebFetch the Cost Optimization URL in `shared/live-sources.md`.
- The cookbook **Cost optimization on the Claude API** (`https://platform.claude.com/cookbook/cost-optimization-cost-optimization`) - a runnable end-to-end worked example of this workflow.
- The **Usage and Cost Admin API** docs - the URL in `shared/live-sources.md`; the endpoint reference pages linked from that page carry the full parameter and response schemas.
- Per-model prices: always the **Pricing** URL in `shared/live-sources.md`, never remembered rates.
