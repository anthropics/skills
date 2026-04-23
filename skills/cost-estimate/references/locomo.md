# LOCOMO — LLM-regeneration cost (counterfactual)

COCOMO answers "what did humans cost to build this?". LOCOMO (popularised by `scc`) answers the counterfactual:

> "What would it cost an LLM to re-generate this code from spec today?"

It's a useful *floor* for Claude-ROI discussions.

## Formula

```
tokens_per_loc        ≈ 4           # empirical: ~4 tokens per line of code for generation
iteration_factor      = 3           # typical: 3 generation passes before acceptance
input_prompt_overhead = 2           # spec + context tokens per code token
regen_tokens          = SLOC × tokens_per_loc × (1 + input_prompt_overhead) × iteration_factor

# Claude rates (Opus tier): assume 10% input / 90% output token mix
# Use current published Anthropic per-token rates. See scripts/claude_token_cost.py
# for ground-truth rates used elsewhere in this skill.
api_cost = regen_tokens × (0.1 × in_rate + 0.9 × out_rate) / 1_000_000

# Human review time to accept LLM output
review_hours = SLOC / 1000   # ~1 hr per KLOC to read/accept generated code
review_cost  = review_hours × recommended_rate

locomo_cost_usd = api_cost + review_cost
locomo_hours    = review_hours          # the only *human* hours LOCOMO implies
```

## Reporting

Report three numbers side-by-side in the final output:

| Method | Hours | USD | Interpretation |
|---|---|---|---|
| COCOMO II (top-down, human) | [H1] | [$1] | Traditional human build cost |
| Bottom-up (Step 3+5) | [H2] | [$2] | Category-rate, human build cost |
| **LOCOMO (LLM regen + review)** | [H3] | [$3] | **Floor: what re-generating costs today** |

The ratio `COCOMO_cost / LOCOMO_cost` is a **human premium multiple**. If a codebase costs $500k by COCOMO and $15k by LOCOMO, the **33× human premium** is where Claude ROI actually comes from — flag it explicitly in the Claude ROI section.

## Caveats

- LOCOMO assumes a complete spec exists (it usually doesn't).
- It ignores novel-problem effort.
- It undercounts domains where correctness is load-bearing (crypto, embedded, safety-critical).
- Never publish LOCOMO *alone* — only alongside COCOMO and bottom-up.
