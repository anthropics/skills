# v1.0 vs v2.0 Diff Report

## What changed

1. **27 descriptions rewritten** as cross-domain triggers (mentions "Load seal-X if..." explicitly)
2. **Gotchas sections added** to all 27 skills (0→27)
3. **Avg description length**: 130 → 358 chars (+175%)

## Test results (Claude Code, 20 prompts)

| Metric | v1.0 | v2.0 | Change |
|---|---|---|---|
| Overall average | 4.75 | 4.85 | +0.10 |
| Multi-domain avg | 4.50 | 4.75 | +0.25 |
| Gotcha detection | 5.0 | 5.0 | — |
| False positive rate | 0% | 0% | — |

## Prompts that improved

| Prompt | v1.0 | v2.0 | Why |
|---|---|---|---|
| #8 Telegram + incident | 4 | 5 | Description now mentions loading incident-management explicitly |
| #12 Treasury signer | 4 | 5 | Description now mentions loading iam explicitly |

## Remaining gaps

| Prompt | Score | Issue |
|---|---|---|
| #11 Audit dev pipeline | 4 | Missed co-loading seal-supply-chain |
| #17 VPN for comms | 4 | Missed co-loading seal-encryption |
| #20 Hot vs cold wallets | 4 | Slightly surface-level answer |

## Conclusion

Cross-domain triggers in descriptions are the biggest lever. v2.0 fixed 2 of 3 multi-domain under-loads. Remaining 3 prompts would need explicit "also load seal-X for Y scenario" additions to their descriptions.
