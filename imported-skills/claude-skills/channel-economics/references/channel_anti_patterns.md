# Channel Anti-Patterns

The eight anti-patterns this skill is built to detect, with citations. Most channel-economics decisions fail because of these patterns, not because the math is wrong.

---

## 1. Channel-led deals from your own pipeline = direct cost + partner cut

**Pattern:** Your AE sources an account, qualifies it, runs discovery, scopes the solution — and then a partner gets attached at the contract stage for the partner cut. The deal closes, is reported as "channel-sourced", and the partner gets margin.

**Why it kills:** You paid full direct cost (AE time, SE time, marketing) AND gave away partner margin. The deal looks profitable as "channel-led" but is value-destroying in reality.

**Detection:** require **first-touch attribution** in CRM. If the first-touch is internal but the deal closes as channel-sourced, flag it.

Source: Forrester Research, *The Channel-Influence vs. Channel-Source Gap*, 2019. Industry data: 25-40% of "channel-sourced" deals are actually channel-influenced direct deals.

---

## 2. No overhead allocation = false partner-margin lift

**Pattern:** Partner channel reports 75% gross margin while direct reports 60%. Look closer: direct channel gets 25% overhead allocation; partner channel gets 5% "because the partner handles overhead." The partner does not, in fact, handle overhead — your channel manager, partner program, MDF, and certification are all in YOUR P&L.

**Why it kills:** Apparent partner-margin lift drives over-investment in partner program. When the executive team eventually does honest allocation, partner margin collapses 8-15 points.

**Detection:** validate overhead-% is **consistent** across channels. If partner overhead allocation is <50% of direct, flag for review.

Source: Tomasz Tunguz, *The Hidden Costs of Channel Programs*, tomtunguz.com analyses 2021-2023. See also Horngren on allocation consistency.

---

## 3. Ignoring enablement time as cost

**Pattern:** Your AE spends 4 hours/week on partner co-selling, your SE spends 6 hours/week on partner technical enablement, your CS team handles tier-2 support that partners offload. None of this is loaded into channel cost.

**Why it kills:** Partner enablement time is often 15-30% of total channel cost, completely unattributed. The channel looks far more efficient than it is.

**Detection:** `cost_to_serve_calculator.py` flags `partner_enablement_time` and `certification_investment` when left at $0.

Source: Jay McBain (Canalys), *State of the Channel* research; Joe Hessling, *Partner Program ROI Studies* (channeltivity.com). Industry data: time-tracked enablement attribution increases partner channel cost by 15-30% over naive accounting.

---

## 4. MDF without ROI tracking

**Pattern:** Market Development Funds disbursed to partners without an attributable pipeline ROI. Partners take the MDF, deliver an event or campaign of dubious value, and no pipeline is traceable to the spend.

**Why it kills:** MDF without attribution is just a partner discount in disguise — and undisciplined. Industry-median MDF-to-pipeline ratio is 3.5:1; best-in-class is >7:1. If yours is <3:1 (or untracked), you have an unbudgeted discount line.

**Detection:** require MDF requests to commit to attributable pipeline targets BEFORE disbursement. Reconcile quarterly.

Source: Jay McBain (Canalys), MDF discipline research. SiriusDecisions (now Forrester) MDF benchmarks: 60% of MDF spend has no attributable pipeline tracking at all.

---

## 5. Channel-mix dogma ("we don't sell direct") blocks profitable segments

**Pattern:** A founder or CRO has a strong belief — "we're a partner-first company", "we don't sell direct in SMB", "we never sell direct in EMEA" — that overrides the segment-level economics. Profitable segments get starved because the strategy slogan doesn't allow direct motion there.

**Why it kills:** Mix should follow the math. Industry data shows dogmatic single-channel strategies forfeit 15-25% of TAM in mid-market specifically.

**Detection:** force the explicit articulation of the dogma in the planning conversation. "What's the segment we DON'T sell into, and why?"

Source: MIT Sloan Management Review, *When Channel Conflict Means Growth*, Frazier & Lassar (1996, updated 2019). Also: HBR on channel-conflict mismanagement, Cespedes (2014).

---

## 6. Treating influenced as sourced

**Pattern:** Partner is involved somewhere in a deal cycle — sometimes only at signature — and the deal is reported as "channel-sourced." Influence and source get conflated.

**Why it kills:** Inflates partner contribution by 25-40%. Drives mis-allocation of channel investment. Channel-program ROI becomes uninterpretable.

**Detection:** require strict first-touch + qualified-source criteria. Channel-sourced = partner originated the opportunity AND brought it to your team unqualified.

Source: SiriusDecisions (now Forrester), *Channel Attribution Models*, 2018-2022 research. Single most-cited source-vs-influence taxonomy in B2B SaaS.

---

## 7. No cost-attribution for channel-manager headcount

**Pattern:** Channel manager salary ($150-$250k loaded) is bucketed under "G&A" or "Sales Overhead" rather than attributed to the channel they manage. The channel reports better economics because its biggest cost line is hidden.

**Why it kills:** A $200k channel manager managing $4M of partner ARR is $50 of channel-manager cost per $1k ARR — material to the channel verdict. Hiding it is the most common single-line distortion in channel economics.

**Detection:** `cost_to_serve_calculator.py` flags `channel_manager_attribution` at $0 as a hidden-cost line.

Source: Gartner, *Service Delivery Cost Allocation in Multi-Channel Technology Vendors*, 2022. McKinsey CTS research.

---

## 8. Channel ROI computed without retention differential

**Pattern:** Channel ROI calculation uses pooled retention assumption (e.g., 90% across all channels) when in fact partner-sourced customers retain at 84% and direct-sourced retain at 92%. LTV calculation is inflated for the partner channel.

**Why it kills:** A 5-point retention gap moves LTV by 30-50%. Most channel investment decisions are made on LTV, so the wrong retention assumption produces the wrong investment decision.

**Detection:** require **per-channel retention** as mandatory input. `channel_mix_optimizer.py` will not compute effective LTV without a per-channel retention number.

Source: David Skok (*For Entrepreneurs* — SaaS Metrics 2.0). LTV = (ARPA × Gross Margin) / Churn — channel-blind churn is the most common source of false channel ROI.

---

## Bonus anti-pattern: the "we'll figure out attribution later" trap

**Pattern:** Channel program launches without an attribution model. Six quarters later, no one can answer "did this work?" because the data was never structured.

**Why it kills:** Attribution must be designed at program-launch, not retrofit. Retroactive attribution is always contested.

**Detection:** force the attribution model to be in writing BEFORE the channel program is launched.

Source: HBR, *Why Channel Programs Fail* (Cespedes, 2014). Also: Tomasz Tunguz on channel-trap analyses.

---

## How this skill detects the anti-patterns

| Anti-pattern | Detection mechanism |
|---|---|
| 1. Channel-led from own pipeline | Forcing question #3 (influence vs. source) |
| 2. No overhead allocation | `cost_to_serve_calculator.py` warns on inconsistent overhead-% |
| 3. Ignoring enablement time | Hidden-cost flag on `partner_enablement_time` |
| 4. MDF without ROI | Forcing question #5 (MDF ratio) |
| 5. Mix dogma | Forcing question #6 |
| 6. Influenced as sourced | Forcing question #3 |
| 7. No channel-manager attribution | Hidden-cost flag on `channel_manager_attribution` |
| 8. No retention differential | Forcing question #2; mandatory per-channel input |
